// Copyright 2016 Mozilla Foundation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(unused_imports, dead_code, unused_variables)]

use crate::compiler::args::*;
use crate::compiler::c::{CCompilerImpl, CCompilerKind, ParsedArguments};
use crate::compiler::gcc::ArgData::*;
use crate::compiler::{gcc, write_temp_file, Cacheable, CompileCommand, CompilerArguments};
use crate::dist;
use crate::mock_command::{CommandCreator, CommandCreatorSync, RunCommand};
use crate::util::{run_input_output, OsStrExt};
use std::ffi::OsString;
use std::fs::File;
use std::future::Future;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process;

use crate::errors::*;

/// A struct on which to implement `CCompilerImpl`.
#[derive(Clone, Debug)]
pub struct Clang;

#[async_trait]
impl CCompilerImpl for Clang {
    fn kind(&self) -> CCompilerKind {
        CCompilerKind::Clang
    }
    fn parse_arguments(
        &self,
        arguments: &[OsString],
        cwd: &Path,
        base_dir: Option<&PathBuf>,
        #[cfg(feature = "dist-client")] rewrite_includes_only: bool,
    ) -> CompilerArguments<ParsedArguments> {
        gcc::parse_arguments(
            arguments,
            cwd,
            base_dir,
            #[cfg(feature = "dist-client")]
            rewrite_includes_only,
            #[cfg(feature = "dist-client")]
            self.kind(),
            (&gcc::ARGS[..], &ARGS[..]),
        )
    }

    #[allow(clippy::too_many_arguments)]
    async fn preprocess<T>(
        &self,
        creator: &T,
        executable: &Path,
        parsed_args: &ParsedArguments,
        cwd: &Path,
        env_vars: &[(OsString, OsString)],
        may_dist: bool,
    ) -> Result<process::Output>
    where
        T: CommandCreatorSync,
    {
        gcc::preprocess(creator, executable, parsed_args, cwd, env_vars, may_dist).await
    }

    fn generate_compile_commands(
        &self,
        path_transformer: &mut dist::PathTransformer,
        executable: &Path,
        parsed_args: &ParsedArguments,
        cwd: &Path,
        env_vars: &[(OsString, OsString)],
    ) -> Result<(CompileCommand, Option<dist::CompileCommand>, Cacheable)> {
        gcc::generate_compile_commands(path_transformer, executable, parsed_args, cwd, env_vars)
    }
}

counted_array!(pub static ARGS: [ArgInfo<gcc::ArgData>; _] = [
    take_arg!("--serialize-diagnostics", OsString, Separated, PassThrough),
    take_arg!("--target", OsString, Separated, PassThrough),
    take_arg!("-Xclang", OsString, Separated, XClang),
    take_arg!("-add-plugin", OsString, Separated, PassThrough),
    take_arg!("-debug-info-kind", OsString, Concatenated('='), PassThrough),
    take_arg!("-dependency-file", PathBuf, Separated, DepArgumentPath),
    flag!("-fcolor-diagnostics", DiagnosticsColorFlag),
    flag!("-fcxx-modules", TooHardFlag),
    take_arg!("-fdebug-compilation-dir", OsString, Separated, PassThrough),
    flag!("-fmodules", TooHardFlag),
    flag!("-fno-color-diagnostics", NoDiagnosticsColorFlag),
    take_arg!("-fplugin", PathBuf, CanBeConcatenated('='), ExtraHashFile),
    flag!("-fprofile-instr-generate", ProfileGenerate),
    // Can be either -fprofile-instr-use or -fprofile-instr-use=path
    take_arg!("-fprofile-instr-use", OsString, Concatenated, TooHard),
    take_arg!("-fsanitize-blacklist", PathBuf, Concatenated('='), ExtraHashFile),
    take_arg!("-gcc-toolchain", OsString, Separated, PassThrough),
    take_arg!("-include-pch", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-ivfsoverlay", PathBuf, CanBeConcatenated('='), PreprocessorArgumentPath),
    take_arg!("-load", PathBuf, Separated, ExtraHashFile),
    take_arg!("-mllvm", OsString, Separated, PassThrough),
    take_arg!("-plugin-arg", OsString, Concatenated('-'), PassThrough),
    take_arg!("-target", OsString, Separated, PassThrough),
    flag!("-verify", PreprocessorArgumentFlag),
]);

#[cfg(test)]
mod test {
    use super::*;
    use crate::compiler::gcc;
    use crate::compiler::*;
    use crate::mock_command::*;
    use crate::test::utils::*;
    use std::collections::HashMap;
    use std::future::Future;
    use std::path::PathBuf;

    fn parse_arguments_(arguments: Vec<String>) -> CompilerArguments<ParsedArguments> {
        let arguments = arguments.iter().map(OsString::from).collect::<Vec<_>>();
        Clang.parse_arguments(
            &arguments,
            &std::env::current_dir().unwrap(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        )
    }

    macro_rules! parses {
        ( $( $s:expr ),* ) => {
            match parse_arguments_(vec![ $( $s.to_string(), )* ]) {
                CompilerArguments::Ok(a) => a,
                o => panic!("Got unexpected parse result: {:?}", o),
            }
        }
    }

    #[cfg(feature = "dist-client")]
    fn parse_arguments_rewrite_include_(
        arguments: Vec<String>,
    ) -> CompilerArguments<ParsedArguments> {
        let arguments = arguments.iter().map(OsString::from).collect::<Vec<_>>();
        Clang.parse_arguments(&arguments, &std::env::current_dir().unwrap(), None, true)
    }

    #[cfg(feature = "dist-client")]
    macro_rules! parses_rewrite_include {
        ( $( $s:expr ),* ) => {
            match parse_arguments_rewrite_include_(vec![ $( $s.to_string(), )* ]) {
                CompilerArguments::Ok(a) => a,
                o => panic!("Got unexpected parse result: {:?}", o),
            }
        }
    }

    #[test]
    fn test_parse_arguments_simple() {
        let a = parses!("-c", "foo.c", "-o", "foo.o");
        assert_eq!(Some("foo.c"), a.input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert!(a.preprocessor_args.is_empty());
        assert!(a.common_args.is_empty());
    }

    #[test]
    fn test_parse_arguments_values() {
        let a = parses!(
            "-c", "foo.cxx", "-arch", "xyz", "-fabc", "-I", "include", "-o", "foo.o", "-include",
            "file"
        );
        assert_eq!(Some("foo.cxx"), a.input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-Iinclude", "-include", "file"], a.preprocessor_args);
        assert_eq!(ovec!["-arch", "xyz", "-fabc"], a.common_args);
    }

    #[test]
    fn test_parse_arguments_others() {
        parses!("-c", "foo.c", "-B", "somewhere", "-o", "foo.o");
        parses!(
            "-c",
            "foo.c",
            "-target",
            "x86_64-apple-darwin11",
            "-o",
            "foo.o"
        );
        parses!("-c", "foo.c", "-gcc-toolchain", "somewhere", "-o", "foo.o");
    }

    #[test]
    fn test_parse_arguments_clangmodules() {
        assert_eq!(
            CompilerArguments::CannotCache("-fcxx-modules", None),
            parse_arguments_(stringvec!["-c", "foo.c", "-fcxx-modules", "-o", "foo.o"])
        );
        assert_eq!(
            CompilerArguments::CannotCache("-fmodules", None),
            parse_arguments_(stringvec!["-c", "foo.c", "-fmodules", "-o", "foo.o"])
        );
    }

    #[test]
    fn test_parse_xclang_invalid() {
        assert_eq!(
            CompilerArguments::CannotCache("Can't handle Raw arguments with -Xclang", None),
            parse_arguments_(stringvec![
                "-c", "foo.c", "-o", "foo.o", "-Xclang", "broken"
            ])
        );
        assert_eq!(
            CompilerArguments::CannotCache(
                "argument parse",
                Some("Unexpected end of args".to_string())
            ),
            parse_arguments_(stringvec!["-c", "foo.c", "-o", "foo.o", "-Xclang", "-load"])
        );
    }

    #[test]
    fn test_parse_xclang_load() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-load",
            "-Xclang",
            "plugin.so"
        );
        println!("A {:#?}", a);
        assert_eq!(
            ovec!["-Xclang", "-load", "-Xclang", "plugin.so"],
            a.common_args
        );
        assert_eq!(
            ovec![std::env::current_dir().unwrap().join("plugin.so")],
            a.extra_hash_files
        );
    }

    #[test]
    fn test_parse_xclang_add_plugin() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-add-plugin",
            "-Xclang",
            "foo"
        );
        assert_eq!(
            ovec!["-Xclang", "-add-plugin", "-Xclang", "foo"],
            a.common_args
        );
    }

    #[test]
    fn test_parse_xclang_llvm_stuff() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-mllvm",
            "-Xclang",
            "-instcombine-lower-dbg-declare=0",
            "-Xclang",
            "-debug-info-kind=constructor"
        );
        assert_eq!(
            ovec![
                "-Xclang",
                "-mllvm",
                "-Xclang",
                "-instcombine-lower-dbg-declare=0",
                "-Xclang",
                "-debug-info-kind=constructor"
            ],
            a.common_args
        );
    }

    #[test]
    fn test_parse_xclang_plugin_arg_blink_gc_plugin() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-add-plugin",
            "-Xclang",
            "blink-gc-plugin",
            "-Xclang",
            "-plugin-arg-blink-gc-plugin",
            "-Xclang",
            "no-members-in-stack-allocated"
        );
        assert_eq!(
            ovec![
                "-Xclang",
                "-add-plugin",
                "-Xclang",
                "blink-gc-plugin",
                "-Xclang",
                "-plugin-arg-blink-gc-plugin",
                "-Xclang",
                "no-members-in-stack-allocated"
            ],
            a.common_args
        );
    }

    #[test]
    fn test_parse_xclang_plugin_arg_find_bad_constructs() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-add-plugin",
            "-Xclang",
            "find-bad-constructs",
            "-Xclang",
            "-plugin-arg-find-bad-constructs",
            "-Xclang",
            "check-ipc"
        );
        assert_eq!(
            ovec![
                "-Xclang",
                "-add-plugin",
                "-Xclang",
                "find-bad-constructs",
                "-Xclang",
                "-plugin-arg-find-bad-constructs",
                "-Xclang",
                "check-ipc"
            ],
            a.common_args
        );
    }

    #[test]
    fn test_parse_ivfsoverlay() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-Xclang",
            "-ivfsoverlay",
            "-Xclang",
            "/a/x.yaml"
        );
        assert_eq!(
            ovec!["-Xclang", "-ivfsoverlay", "-Xclang", "/a/x.yaml"],
            a.preprocessor_args
        );
    }

    #[test]
    fn test_parse_xclang_pass_through_unknown() {
        let a = parses!("-c", "foo.c", "-o", "foo.o", "-Xclang", "-gcodeview");
        assert_eq!(ovec!["-Xclang", "-gcodeview"], a.common_args);
    }

    #[test]
    fn test_parse_xclang_verify() {
        let a = parses!("-c", "foo.c", "-o", "foo.o", "-Xclang", "-verify");
        assert_eq!(ovec!["-Xclang", "-verify"], a.preprocessor_args);
    }

    #[test]
    fn test_parse_fplugin() {
        let a = parses!("-c", "foo.c", "-o", "foo.o", "-fplugin", "plugin.so");
        println!("A {:#?}", a);
        assert_eq!(ovec!["-fplugin", "plugin.so"], a.common_args);
        assert_eq!(
            ovec![std::env::current_dir().unwrap().join("plugin.so")],
            a.extra_hash_files
        );
    }

    #[test]
    fn test_parse_fsanitize_blacklist() {
        let a = parses!(
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-fsanitize-blacklist=list.txt"
        );
        assert_eq!(ovec!["-fsanitize-blacklist=list.txt"], a.common_args);
        assert_eq!(
            ovec![std::env::current_dir().unwrap().join("list.txt")],
            a.extra_hash_files
        );
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn test_parse_fsanitize_blacklist_base_dir_success() {
        let args = stringvec![
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-fsanitize-blacklist=/a/b/list.txt"
        ];
        let args = args.iter().map(OsString::from).collect::<Vec<_>>();
        let ParsedArguments {
            extra_hash_files,
            common_args,
            ..
        } = match Clang.parse_arguments(
            &args,
            &PathBuf::from("/a"),
            Some(PathBuf::from("/")).as_ref(),
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };

        assert_eq!(ovec!["-fsanitize-blacklist=b/list.txt"], common_args);
        assert_eq!(ovec!["/a/b/list.txt"], extra_hash_files);
    }

    #[test]
    #[cfg(target_os = "windows")]
    fn test_parse_fsanitize_blacklist_base_dir_success() {
        let args = stringvec![
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            r"-fsanitize-blacklist=C:\a\b\list.txt"
        ];
        let args = args.iter().map(OsString::from).collect::<Vec<_>>();
        let ParsedArguments {
            extra_hash_files,
            common_args,
            ..
        } = match Clang.parse_arguments(
            &args,
            &PathBuf::from(r"C:\a"),
            Some(PathBuf::from(r"C:\")).as_ref(),
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };

        assert_eq!(ovec![r"-fsanitize-blacklist=b\list.txt"], common_args);
        assert_eq!(ovec![r"C:\a\b\list.txt"], extra_hash_files);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn test_parse_fsanitize_blacklist_base_dir_fail() {
        let args = stringvec![
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            "-fsanitize-blacklist=/a/b/list.txt"
        ];
        let args = args.iter().map(OsString::from).collect::<Vec<_>>();
        let ParsedArguments {
            extra_hash_files,
            common_args,
            ..
        } = match Clang.parse_arguments(
            &args,
            &PathBuf::from("/a"),
            Some(PathBuf::from("/a/b/c")).as_ref(),
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };

        assert_eq!(ovec!["-fsanitize-blacklist=/a/b/list.txt"], common_args);
        assert_eq!(ovec!["/a/b/list.txt"], extra_hash_files);
    }

    #[test]
    #[cfg(target_os = "windows")]
    fn test_parse_fsanitize_blacklist_base_dir_fail() {
        let args = stringvec![
            "-c",
            "foo.c",
            "-o",
            "foo.o",
            r"-fsanitize-blacklist=C:\a\b\list.txt"
        ];
        let args = args.iter().map(OsString::from).collect::<Vec<_>>();
        let ParsedArguments {
            extra_hash_files,
            common_args,
            ..
        } = match Clang.parse_arguments(
            &args,
            &PathBuf::from(r"C:\a"),
            Some(PathBuf::from(r"C:\a\b\c")).as_ref(),
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };

        assert_eq!(ovec![r"-fsanitize-blacklist=C:\a\b\list.txt"], common_args);
        assert_eq!(ovec![r"C:\a\b\list.txt"], extra_hash_files);
    }

    #[test]
    fn test_parse_color_diags() {
        let a = parses!("-c", "foo.c", "-o", "foo.o", "-fcolor-diagnostics");
        assert_eq!(a.color_mode, ColorMode::On);

        let a = parses!("-c", "foo.c", "-o", "foo.o", "-fno-color-diagnostics");
        assert_eq!(a.color_mode, ColorMode::Off);

        let a = parses!("-c", "foo.c", "-o", "foo.o");
        assert_eq!(a.color_mode, ColorMode::Auto);
    }

    #[test]
    #[cfg(not(feature = "dist-client"))]
    fn test_parse_arguments_local_no_rewrite_includes() {
        let a = parses!(
            "-nostdinc",
            "-Xclang",
            "-trigraphs",
            "-x",
            "c",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        );

        assert_eq!(Some("foo.c"), a.input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(
            ovec!["-nostdinc", "-Xclang", "-trigraphs"],
            a.preprocessor_args
        );
        assert_eq!(Some("-c"), a.compilation_flag.to_str());
        assert_eq!(ovec!["-xc"], a.common_args);
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_parse_arguments_remote_no_rewrite_includes_dash_x() {
        let a = parses!(
            "-nostdinc",
            "-Xclang",
            "-trigraphs",
            "-x",
            "c",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        );
        assert_eq!(Some("foo.c"), a.input.to_str());
        assert_eq!(Some("foo.c"), a.dist_input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(
            ovec!["-nostdinc", "-xc", "-Xclang", "-trigraphs"],
            a.preprocessor_args
        );
        assert_eq!(Some("-c -x cpp-output"), a.compilation_flag.to_str());
        assert!(a.common_args.is_empty());
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_parse_arguments_remote_no_rewrite_includes_file_extension() {
        let a = parses!(
            "-nostdinc",
            "-Xclang",
            "-trigraphs",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        );
        assert_eq!(Some("foo.c"), a.input.to_str());
        assert_eq!(Some("foo.i"), a.dist_input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(
            ovec!["-nostdinc", "-Xclang", "-trigraphs"],
            a.preprocessor_args
        );
        assert_eq!(Some("-c"), a.compilation_flag.to_str());
        assert!(a.common_args.is_empty());
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_parse_arguments_remote_rewrite_includes() {
        let a = parses_rewrite_include!(
            "-nostdinc",
            "-Xclang",
            "-trigraphs",
            "-x",
            "c",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        );
        assert_eq!(Some("foo.c"), a.input.to_str());
        assert_eq!(Some("foo.c"), a.dist_input.to_str());
        assert_map_contains!(a.outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-frewrite-includes"], a.preprocessor_args);
        assert_eq!(Some("-c"), a.compilation_flag.to_str());
        assert_eq!(
            ovec!["-nostdinc", "-xc", "-Xclang", "-trigraphs"],
            a.common_args
        );
    }
}
