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

use crate::compiler::args::*;
use crate::compiler::c::{make_relative_path, CCompilerImpl, CCompilerKind, ParsedArguments};
use crate::compiler::{clang, Cacheable, ColorMode, CompileCommand, CompilerArguments};
use crate::dist;
use crate::mock_command::{CommandCreatorSync, RunCommand};
use crate::util::{run_input_output, OsStrExt};
use log::Level::Trace;
use std::collections::HashMap;
use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process;

use crate::errors::*;

/// A struct on which to implement `CCompilerImpl`.
#[derive(Clone, Debug)]
pub struct Gcc;

#[async_trait]
impl CCompilerImpl for Gcc {
    fn kind(&self) -> CCompilerKind {
        CCompilerKind::Gcc
    }
    fn parse_arguments(
        &self,
        arguments: &[OsString],
        cwd: &Path,
        base_dir: Option<&PathBuf>,
        #[cfg(feature = "dist-client")] rewrite_includes_only: bool,
    ) -> CompilerArguments<ParsedArguments> {
        parse_arguments(
            arguments,
            cwd,
            base_dir,
            #[cfg(feature = "dist-client")]
            rewrite_includes_only,
            #[cfg(feature = "dist-client")]
            self.kind(),
            &ARGS[..],
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
        preprocess(creator, executable, parsed_args, cwd, env_vars, may_dist).await
    }

    fn generate_compile_commands(
        &self,
        path_transformer: &mut dist::PathTransformer,
        executable: &Path,
        parsed_args: &ParsedArguments,
        cwd: &Path,
        env_vars: &[(OsString, OsString)],
    ) -> Result<(CompileCommand, Option<dist::CompileCommand>, Cacheable)> {
        generate_compile_commands(path_transformer, executable, parsed_args, cwd, env_vars)
    }
}

ArgData! { pub
    TooHardFlag,
    TooHard(OsString),
    DiagnosticsColor(OsString),
    DiagnosticsColorFlag,
    NoDiagnosticsColorFlag,
    // Should only be necessary for -Xclang flags - unknown flags not hidden behind
    // that are assumed to not affect compilation
    PassThrough(OsString),
    PassThroughPath(PathBuf),
    PreprocessorArgumentFlag,
    PreprocessorArgument(OsString),
    PreprocessorArgumentPath(PathBuf),
    DoCompilation,
    Output(PathBuf),
    NeedDepTarget,
    // Though you might think this should be a path as it's a Makefile target,
    // it's not treated as a path by the compiler - it's just written wholesale
    // (including any funny make syntax) into the dep file.
    DepTarget(OsString),
    DepArgumentPath(PathBuf),
    Language(OsString),
    SplitDwarf,
    ProfileGenerate,
    TestCoverage,
    Coverage,
    ExtraHashFile(PathBuf),
    // Only valid for clang, but this needs to be here since clang shares gcc's arg parsing.
    XClang(OsString),
    Arch(OsString),
}

use self::ArgData::*;

// Mostly taken from https://github.com/ccache/ccache/blob/master/src/compopt.c#L32-L84
counted_array!(pub static ARGS: [ArgInfo<ArgData>; _] = [
    flag!("-", TooHardFlag),
    flag!("--coverage", Coverage),
    take_arg!("--param", OsString, Separated, PassThrough),
    flag!("--save-temps", TooHardFlag),
    take_arg!("--serialize-diagnostics", PathBuf, Separated, PassThroughPath),
    take_arg!("--sysroot", PathBuf, Separated, PassThroughPath),
    take_arg!("-A", OsString, Separated, PassThrough),
    take_arg!("-B", PathBuf, CanBeSeparated, PassThroughPath),
    take_arg!("-D", OsString, CanBeSeparated, PassThrough),
    flag!("-E", TooHardFlag),
    take_arg!("-F", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-G", OsString, Separated, PassThrough),
    take_arg!("-I", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-L", OsString, Separated, PassThrough),
    flag!("-M", TooHardFlag),
    flag!("-MD", NeedDepTarget),
    take_arg!("-MF", PathBuf, Separated, DepArgumentPath),
    flag!("-MM", TooHardFlag),
    flag!("-MMD", NeedDepTarget),
    flag!("-MP", NeedDepTarget),
    take_arg!("-MQ", OsString, Separated, DepTarget),
    take_arg!("-MT", OsString, Separated, DepTarget),
    flag!("-P", TooHardFlag),
    take_arg!("-U", OsString, CanBeSeparated, PassThrough),
    take_arg!("-V", OsString, Separated, PassThrough),
    take_arg!("-Xassembler", OsString, Separated, PassThrough),
    take_arg!("-Xlinker", OsString, Separated, PassThrough),
    take_arg!("-Xpreprocessor", OsString, Separated, PreprocessorArgument),
    take_arg!("-arch", OsString, Separated, Arch),
    take_arg!("-aux-info", OsString, Separated, PassThrough),
    take_arg!("-b", OsString, Separated, PassThrough),
    flag!("-c", DoCompilation),
    take_arg!("-fdiagnostics-color", OsString, Concatenated('='), DiagnosticsColor),
    flag!("-fno-diagnostics-color", NoDiagnosticsColorFlag),
    flag!("-fno-working-directory", PreprocessorArgumentFlag),
    flag!("-fplugin=libcc1plugin", TooHardFlag),
    flag!("-fprofile-arcs", ProfileGenerate),
    flag!("-fprofile-generate", ProfileGenerate),
    take_arg!("-fprofile-use", OsString, Concatenated, TooHard),
    flag!("-frepo", TooHardFlag),
    flag!("-fsyntax-only", TooHardFlag),
    flag!("-ftest-coverage", TestCoverage),
    flag!("-fworking-directory", PreprocessorArgumentFlag),
    flag!("-gsplit-dwarf", SplitDwarf),
    take_arg!("-idirafter", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-iframework", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-imacros", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-imultilib", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-include", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-install_name", OsString, Separated, PassThrough),
    take_arg!("-iprefix", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-iquote", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-isysroot", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-isystem", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-iwithprefix", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    take_arg!("-iwithprefixbefore", PathBuf, CanBeSeparated, PreprocessorArgumentPath),
    flag!("-nostdinc", PreprocessorArgumentFlag),
    flag!("-nostdinc++", PreprocessorArgumentFlag),
    take_arg!("-o", PathBuf, CanBeSeparated, Output),
    flag!("-remap", PreprocessorArgumentFlag),
    flag!("-save-temps", TooHardFlag),
    take_arg!("-stdlib", OsString, Concatenated('='), PreprocessorArgument),
    flag!("-trigraphs", PreprocessorArgumentFlag),
    take_arg!("-u", OsString, CanBeSeparated, PassThrough),
    take_arg!("-x", OsString, CanBeSeparated, Language),
    take_arg!("-z", OsString, CanBeSeparated, PassThrough),
    take_arg!("@", OsString, Concatenated, TooHard),
]);

#[cfg(feature = "dist-client")]
fn used_before_rewrite_includes(flag: Option<&'static str>, kind: &CCompilerKind) -> bool {
    let flag = match flag {
        Some(f) => f,
        None => return false,
    };
    // let mut flags = vec![];
    if *kind == CCompilerKind::Gcc {
        // For "-fdirectives-only"
        !vec!["-D", "-U"].contains(&flag)
    // } else if *kind == CCompilerKind::Clang {
    //     // For "-frewrite-includes"
    //     if vec!["-include-pch", "-ivfsoverlay"].contains(&flag) {
    //         false
    //     } else {
    //         // Assume all such kinds of flags are used for finding headers
    //         is_preprocessor_path
    //     }
    } else {
        false
    }
}

/// Parse `arguments`, determining whether it is supported.
///
/// If any of the entries in `arguments` result in a compilation that
/// cannot be cached, return `CompilerArguments::CannotCache`.
/// If the commandline described by `arguments` is not compilation,
/// return `CompilerArguments::NotCompilation`.
/// Otherwise, return `CompilerArguments::Ok(ParsedArguments)`, with
/// the `ParsedArguments` struct containing information parsed from
/// `arguments`.
pub fn parse_arguments<S>(
    arguments: &[OsString],
    cwd: &Path,
    base_dir: Option<&PathBuf>,
    #[cfg(feature = "dist-client")] rewrite_includes_only: bool,
    #[cfg(feature = "dist-client")] kind: CCompilerKind,
    arg_info: S,
) -> CompilerArguments<ParsedArguments>
where
    S: SearchableArgInfo<ArgData>,
{
    let mut output_arg = None;
    let mut input_args = vec![];
    let mut dep_target = None;
    let mut dep_flag = OsString::from("-MT");
    let mut common_args = vec![];
    let mut preprocessor_args = vec![];
    let mut dependency_args = vec![];
    let mut extra_hash_files = vec![];
    let mut compilation = false;
    let mut split_dwarf = false;
    let mut need_explicit_dep_target = false;
    #[cfg(feature = "dist-client")]
    let mut language = None;
    #[cfg(feature = "dist-client")]
    let is_nvcc = kind == CCompilerKind::Nvcc;
    let mut compilation_flag = OsString::new();
    let mut profile_generate = false;
    let mut outputs_gcno = false;
    let mut xclangs: Vec<OsString> = vec![];
    let mut color_mode = ColorMode::Auto;
    let mut seen_arch = None;
    let mut is_common_args;
    let path_transformer_fn = &|p: &PathBuf| make_relative_path(cwd, base_dir, p);

    // Custom iterator to expand `@` arguments which stand for reading a file
    // and interpreting it as a list of more arguments.
    let it = ExpandIncludeFile::new(cwd, arguments);
    for arg in ArgsIter::new(it, vec!['-'], arg_info) {
        let arg = try_or_cannot_cache!(arg, "argument parse");
        // Check if the value part of this argument begins with '@'. If so, we either
        // failed to expand it, or it was a concatenated argument - either way, bail.
        // We refuse to cache concatenated arguments (like "-include@foo") because they're a
        // mess. See https://github.com/mozilla/sccache/issues/150#issuecomment-318586953
        match arg {
            Argument::WithValue(_, ref v, ArgDisposition::Separated)
            | Argument::WithValue(_, ref v, ArgDisposition::CanBeConcatenated(_))
            | Argument::WithValue(_, ref v, ArgDisposition::CanBeSeparated(_)) => {
                if v.clone()
                    .into_arg_os_string(path_transformer_fn)
                    .unwrap()
                    .starts_with("@")
                {
                    cannot_cache!("@");
                }
            }
            // Empirically, concatenated arguments appear not to interpret '@' as
            // an include directive, so just continue.
            Argument::WithValue(_, _, ArgDisposition::Concatenated(_))
            | Argument::Raw(_)
            | Argument::UnknownFlag(_)
            | Argument::Flag(_, _) => {}
        }

        match arg.get_data() {
            Some(TooHardFlag) | Some(TooHard(_)) => {
                cannot_cache!(arg.flag_str().expect("Can't be Argument::Raw/UnknownFlag",))
            }
            Some(SplitDwarf) => split_dwarf = true,
            Some(DoCompilation) => {
                compilation = true;
                compilation_flag =
                    OsString::from(arg.flag_str().expect("Compilation flag expected"));
            }
            Some(ProfileGenerate) => profile_generate = true,
            Some(TestCoverage) => outputs_gcno = true,
            Some(Coverage) => {
                outputs_gcno = true;
                profile_generate = true;
            }
            Some(DiagnosticsColorFlag) => color_mode = ColorMode::On,
            Some(NoDiagnosticsColorFlag) => color_mode = ColorMode::Off,
            Some(DiagnosticsColor(value)) => {
                color_mode = match value.to_str().unwrap_or("auto") {
                    "" | "always" => ColorMode::On,
                    "never" => ColorMode::Off,
                    _ => ColorMode::Auto,
                };
            }
            Some(Output(p)) => output_arg = Some(p.clone()),
            Some(NeedDepTarget) => need_explicit_dep_target = true,
            Some(DepTarget(s)) => {
                dep_flag = OsString::from(arg.flag_str().expect("Dep target flag expected"));
                dep_target = Some(s.clone());
            }
            Some(DepArgumentPath(_))
            | Some(ExtraHashFile(_))
            | Some(PreprocessorArgumentFlag)
            | Some(PreprocessorArgument(_))
            | Some(PreprocessorArgumentPath(_))
            | Some(PassThrough(_))
            | Some(PassThroughPath(_)) => {}
            #[cfg(not(feature = "dist-client"))]
            Some(Language(_)) => {}
            #[cfg(feature = "dist-client")]
            Some(Language(lang)) => language = Some(lang.clone()),
            Some(Arch(arch)) => {
                match seen_arch {
                    Some(s) if &s != arch => cannot_cache!("multiple different -arch"),
                    _ => {}
                };
                seen_arch = Some(arch.clone());
            }
            Some(XClang(s)) => xclangs.push(s.clone()),
            None => match arg {
                Argument::Raw(ref val) => input_args.push(val.clone()),
                Argument::UnknownFlag(_) => {}
                _ => unreachable!(),
            },
        }
        is_common_args = false;
        let args = match arg.get_data() {
            Some(SplitDwarf)
            | Some(ProfileGenerate)
            | Some(TestCoverage)
            | Some(Coverage)
            | Some(DiagnosticsColor(_))
            | Some(DiagnosticsColorFlag)
            | Some(NoDiagnosticsColorFlag)
            | Some(Arch(_))
            | Some(PassThrough(_))
            | Some(PassThroughPath(_)) => {
                is_common_args = true;
                &mut common_args
            }
            Some(ExtraHashFile(path)) => {
                extra_hash_files.push(cwd.join(path));
                is_common_args = true;
                &mut common_args
            }
            Some(PreprocessorArgumentFlag)
            | Some(PreprocessorArgument(_))
            | Some(PreprocessorArgumentPath(_)) => {
                #[cfg(not(feature = "dist-client"))]
                let args = &mut preprocessor_args;
                #[cfg(feature = "dist-client")]
                let args = if rewrite_includes_only
                    && !used_before_rewrite_includes(arg.flag_str(), &kind)
                {
                    is_common_args = true;
                    &mut common_args
                } else {
                    &mut preprocessor_args
                };
                args
            }
            Some(Language(_)) => {
                #[cfg(not(feature = "dist-client"))]
                let args = {
                    is_common_args = true;
                    &mut common_args
                };
                #[cfg(feature = "dist-client")]
                let args = if rewrite_includes_only || is_nvcc {
                    is_common_args = true;
                    &mut common_args
                } else {
                    // compilation flag would have "cpp-output" suffix
                    &mut preprocessor_args
                };
                args
            }
            Some(DepArgumentPath(_)) | Some(NeedDepTarget) => &mut dependency_args,
            Some(DoCompilation) | Some(Output(_)) | Some(XClang(_)) | Some(DepTarget(_)) => {
                continue
            }
            Some(TooHardFlag) | Some(TooHard(_)) => unreachable!(),
            None => match arg {
                Argument::Raw(_) => continue,
                Argument::UnknownFlag(_) => {
                    is_common_args = true;
                    &mut common_args
                }
                _ => unreachable!(),
            },
        };

        // Normalize attributes such as "-I foo", "-D FOO=bar", as
        // "-Ifoo", "-DFOO=bar", etc. and "-includefoo", "idirafterbar" as
        // "-include foo", "-idirafter bar", etc.
        let norm = match arg.flag_str() {
            Some(s) if s.len() == 2 => NormalizedDisposition::Concatenated,
            _ => NormalizedDisposition::Separated,
        };
        if is_common_args {
            for arg in arg.normalize(norm).iter_os_strings2(path_transformer_fn) {
                args.push(try_string_arg!(arg))
            }
        } else {
            args.extend(arg.normalize(norm).iter_os_strings());
        }
    }

    let xclang_it = ExpandIncludeFile::new(cwd, &xclangs);
    let mut follows_plugin_arg = false;
    for arg in ArgsIter::new(xclang_it, vec!['-'], (&ARGS[..], &clang::ARGS[..])) {
        is_common_args = false;
        let arg = try_or_cannot_cache!(arg, "argument parse");
        let args = match arg.get_data() {
            Some(SplitDwarf)
            | Some(ProfileGenerate)
            | Some(TestCoverage)
            | Some(Coverage)
            | Some(DoCompilation)
            | Some(Language(_))
            | Some(Output(_))
            | Some(TooHardFlag)
            | Some(XClang(_))
            | Some(TooHard(_)) => cannot_cache!(arg
                .flag_str()
                .unwrap_or("Can't handle complex arguments through clang",)),
            None => match arg {
                Argument::Raw(_) if follows_plugin_arg => {
                    is_common_args = true;
                    &mut common_args
                }
                Argument::Raw(_) => cannot_cache!("Can't handle Raw arguments with -Xclang"),
                Argument::UnknownFlag(_) => {
                    is_common_args = true;
                    &mut common_args
                }
                _ => unreachable!(),
            },
            Some(DiagnosticsColor(_))
            | Some(DiagnosticsColorFlag)
            | Some(NoDiagnosticsColorFlag)
            | Some(Arch(_))
            | Some(PassThrough(_))
            | Some(PassThroughPath(_)) => {
                is_common_args = true;
                &mut common_args
            }
            Some(ExtraHashFile(path)) => {
                extra_hash_files.push(cwd.join(path));
                is_common_args = true;
                &mut common_args
            }
            Some(PreprocessorArgumentFlag)
            | Some(PreprocessorArgument(_))
            | Some(PreprocessorArgumentPath(_)) => {
                #[cfg(not(feature = "dist-client"))]
                let args = &mut preprocessor_args;
                #[cfg(feature = "dist-client")]
                let args = if rewrite_includes_only
                    && !used_before_rewrite_includes(arg.flag_str(), &kind)
                {
                    is_common_args = true;
                    &mut common_args
                } else {
                    &mut preprocessor_args
                };
                args
            }
            Some(DepTarget(_)) | Some(DepArgumentPath(_)) | Some(NeedDepTarget) => {
                &mut dependency_args
            }
        };
        follows_plugin_arg = match arg.flag_str() {
            Some(s) => s == "-plugin-arg",
            _ => false,
        };

        // Normalize attributes such as "-I foo", "-D FOO=bar", as
        // "-Ifoo", "-DFOO=bar", etc. and "-includefoo", "idirafterbar" as
        // "-include foo", "-idirafter bar", etc.
        let norm = match arg.flag_str() {
            Some(s) if s.len() == 2 => NormalizedDisposition::Concatenated,
            _ => NormalizedDisposition::Separated,
        };
        if is_common_args {
            for arg in arg.normalize(norm).iter_os_strings2(path_transformer_fn) {
                args.push("-Xclang".into());
                args.push(try_string_arg!(arg));
            }
        } else {
            for arg in arg.normalize(norm).iter_os_strings() {
                args.push("-Xclang".into());
                args.push(arg);
            }
        }
    }

    // We only support compilation.
    if !compilation {
        return CompilerArguments::NotCompilation;
    }
    // Can't cache compilations with multiple inputs.
    if input_args.is_empty() {
        cannot_cache!("no input file");
    } else if input_args.len() > 1 {
        let mut error_msg = OsString::new();
        for (i, input_arg) in input_args.iter().enumerate() {
            if i > 0 {
                error_msg.push(", ");
            }
            error_msg.push(input_arg);
        }
        trace!(
            "multiple input files or possibly unknown arguments: {:?}",
            error_msg
        );
        cannot_cache!("multiple input files");
    }
    let input = &input_args[0];
    let mut outputs = HashMap::new();
    let output = match output_arg {
        // We can't cache compilation that doesn't go to a file
        None => PathBuf::from(Path::new(input).with_extension("o").file_name().unwrap()),
        Some(o) => o,
    };
    if split_dwarf {
        let dwo = output.with_extension("dwo");
        outputs.insert("dwo", dwo);
    }
    if outputs_gcno {
        let gcno = output.with_extension("gcno");
        outputs.insert("gcno", gcno);
        profile_generate = true;
    }
    if need_explicit_dep_target {
        dependency_args.push(dep_flag);
        dependency_args.push(dep_target.unwrap_or_else(|| output.clone().into_os_string()));
    }
    outputs.insert("obj", output);

    #[cfg(feature = "dist-client")]
    if rewrite_includes_only {
        // Move include related flags to common_args
        match kind {
            CCompilerKind::Clang => preprocessor_args.push("-frewrite-includes".into()),
            CCompilerKind::Gcc => {
                // From https://gcc.gnu.org/onlinedocs/gcc/Preprocessor-Options.html:
                //
                // -fdirectives-only
                //
                //     [...]
                //
                //     With -fpreprocessed, predefinition of command line and most
                //     builtin macros is disabled. Macros such as __LINE__, which
                //     are contextually dependent, are handled normally. This
                //     enables compilation of files previously preprocessed with -E
                //     -fdirectives-only.
                //
                // Which is exactly what we do :-)
                common_args.push("-fdirectives-only".into());
                compilation_flag.push(" -fpreprocessed");
            }
            _ => {}
        }
    }

    #[cfg(feature = "dist-client")]
    let dist_input: PathBuf = if rewrite_includes_only || is_nvcc {
        // nvcc does not support `-x cu-cpp-output` or `.cui`
        input.into()
    } else {
        match language {
            // Use -x, no need change input file name.
            Some(l) if l == "c" => {
                compilation_flag.push(" -x cpp-output");
                input.into()
            }
            Some(l) => {
                compilation_flag.push(" -x ");
                compilation_flag.push(l);
                compilation_flag.push("-cpp-output");
                input.into()
            }
            // No -x, change input file name to hint the compiler that the input is preprocessed.
            None => {
                lazy_static! {
                    static ref MAP: HashMap<&'static str, &'static str> = [
                        ("c", "i"),
                        ("cc", "ii"),
                        ("cp", "ii"),
                        ("cxx", "ii"),
                        ("cpp", "ii"),
                        ("CPP", "ii"),
                        ("c++", "ii"),
                        ("C", "ii"),
                        ("m", "mi"),
                        ("mm", "mii"),
                        ("M", "mii"),
                        ("cu", "cui"),
                    ]
                    .iter()
                    .copied()
                    .collect();
                }
                let input: PathBuf = input.into();
                match input.extension().map(|e| e.to_str()) {
                    Some(Some(e)) => match MAP.get(e) {
                        Some(i) => input.with_extension(i),
                        None => input,
                    },
                    _ => input,
                }
            }
        }
    };

    CompilerArguments::Ok(ParsedArguments {
        input: input.into(),
        #[cfg(feature = "dist-client")]
        dist_input,
        compilation_flag,
        depfile: None,
        outputs,
        dependency_args,
        preprocessor_args,
        common_args,
        extra_hash_files,
        msvc_show_includes: false,
        profile_generate,
        color_mode,
    })
}

#[allow(clippy::too_many_arguments)]
pub async fn preprocess<T>(
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
    trace!("preprocess");
    let mut cmd = creator.clone().new_command_sync(executable);
    cmd.arg("-E");
    // When performing distributed compilation, line number info is important for error
    // reporting and to not cause spurious compilation failure (e.g. no exceptions build
    // fails due to exceptions transitively included in the stdlib).
    // With -fprofile-generate line number information is important, so don't use -P.
    if !may_dist && !parsed_args.profile_generate {
        cmd.arg("-P");
    }
    cmd.arg(&parsed_args.input)
        .args(&parsed_args.preprocessor_args)
        .args(&parsed_args.dependency_args)
        .args(&parsed_args.common_args)
        .env_clear()
        .envs(env_vars.iter().map(|&(ref k, ref v)| (k, v)))
        .current_dir(cwd);

    if log_enabled!(Trace) {
        trace!("preprocess: {:?}", cmd);
    }
    run_input_output(cmd, None).await
}

pub fn generate_compile_commands(
    path_transformer: &mut dist::PathTransformer,
    executable: &Path,
    parsed_args: &ParsedArguments,
    cwd: &Path,
    env_vars: &[(OsString, OsString)],
) -> Result<(CompileCommand, Option<dist::CompileCommand>, Cacheable)> {
    // Unused arguments
    #[cfg(not(feature = "dist-client"))]
    {
        let _ = path_transformer;
    }

    trace!("compile");

    let out_file = match parsed_args.outputs.get("obj") {
        Some(obj) => obj,
        None => return Err(anyhow!("Missing object file output")),
    };

    let mut arguments: Vec<OsString> = vec![
        parsed_args.compilation_flag.clone(),
        parsed_args.input.clone().into(),
        "-o".into(),
        out_file.into(),
    ];
    arguments.extend(parsed_args.preprocessor_args.clone());
    arguments.extend(parsed_args.common_args.clone());
    let command = CompileCommand {
        executable: executable.to_owned(),
        arguments,
        env_vars: env_vars.to_owned(),
        cwd: cwd.to_owned(),
    };

    #[cfg(not(feature = "dist-client"))]
    let dist_command = None;
    #[cfg(feature = "dist-client")]
    let dist_command = (|| {
        // https://gcc.gnu.org/onlinedocs/gcc-4.9.0/gcc/Overall-Options.html
        let mut arguments: Vec<String> = vec![
            parsed_args.compilation_flag.clone().into_string().ok()?,
            path_transformer.as_dist(&parsed_args.dist_input)?,
            "-o".into(),
            path_transformer.as_dist(out_file)?,
        ];
        arguments.extend(dist::osstrings_to_strings(&parsed_args.common_args)?);
        Some(dist::CompileCommand {
            executable: path_transformer.as_dist(executable)?,
            arguments,
            env_vars: dist::osstring_tuples_to_strings(env_vars)?,
            cwd: path_transformer.as_dist_abs(cwd)?,
        })
    })();

    Ok((command, dist_command, Cacheable::Yes))
}

pub struct ExpandIncludeFile<'a> {
    cwd: &'a Path,
    stack: Vec<OsString>,
}

impl<'a> ExpandIncludeFile<'a> {
    pub fn new(cwd: &'a Path, args: &[OsString]) -> Self {
        ExpandIncludeFile {
            stack: args.iter().rev().map(|a| a.to_owned()).collect(),
            cwd,
        }
    }
}

impl<'a> Iterator for ExpandIncludeFile<'a> {
    type Item = OsString;

    fn next(&mut self) -> Option<OsString> {
        loop {
            let arg = match self.stack.pop() {
                Some(arg) => arg,
                None => return None,
            };
            let file = match arg.split_prefix("@") {
                Some(arg) => self.cwd.join(&arg),
                None => return Some(arg),
            };

            // According to gcc [1], @file means:
            //
            //     Read command-line options from file. The options read are
            //     inserted in place of the original @file option. If file does
            //     not exist, or cannot be read, then the option will be
            //     treated literally, and not removed.
            //
            //     Options in file are separated by whitespace. A
            //     whitespace character may be included in an option by
            //     surrounding the entire option in either single or double
            //     quotes. Any character (including a backslash) may be
            //     included by prefixing the character to be included with
            //     a backslash. The file may itself contain additional
            //     @file options; any such options will be processed
            //     recursively.
            //
            // So here we interpret any I/O errors as "just return this
            // argument". Currently we don't implement handling of arguments
            // with quotes, so if those are encountered we just pass the option
            // through literally anyway.
            //
            // At this time we interpret all `@` arguments above as non
            // cacheable, so if we fail to interpret this we'll just call the
            // compiler anyway.
            //
            // [1]: https://gcc.gnu.org/onlinedocs/gcc/Overall-Options.html#Overall-Options
            let mut contents = String::new();
            let res = File::open(&file).and_then(|mut f| f.read_to_string(&mut contents));
            if let Err(e) = res {
                debug!("failed to read @-file `{}`: {}", file.display(), e);
                return Some(arg);
            }
            if contents.contains('"') || contents.contains('\'') {
                return Some(arg);
            }
            let new_args = contents.split_whitespace().collect::<Vec<_>>();
            self.stack.extend(new_args.iter().rev().map(|s| s.into()));
        }
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;
    use std::io::Write;

    use super::*;
    use crate::compiler::*;
    use crate::mock_command::*;
    use crate::test::utils::*;

    fn parse_arguments_(arguments: Vec<String>) -> CompilerArguments<ParsedArguments> {
        let args = arguments.iter().map(OsString::from).collect::<Vec<_>>();
        parse_arguments(
            &args,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
            #[cfg(feature = "dist-client")]
            CCompilerKind::Gcc,
            &ARGS[..],
        )
    }

    #[cfg(feature = "dist-client")]
    fn parse_arguments_rewrite_include_(
        arguments: Vec<String>,
    ) -> CompilerArguments<ParsedArguments> {
        let args = arguments.iter().map(OsString::from).collect::<Vec<_>>();
        parse_arguments(
            &args,
            ".".as_ref(),
            None,
            true,
            CCompilerKind::Gcc,
            &ARGS[..],
        )
    }

    #[test]
    fn test_parse_arguments_simple() {
        let args = stringvec!["-c", "foo.c", "-o", "foo.o"];
        let ParsedArguments {
            input,
            compilation_flag,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_eq!(Some("-c"), compilation_flag.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert!(common_args.is_empty());
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_default_name() {
        let args = stringvec!["-c", "foo.c"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert!(common_args.is_empty());
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_default_outputdir() {
        let args = stringvec!["-c", "/tmp/foo.c"];
        let ParsedArguments { outputs, .. } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
    }

    #[test]
    fn test_parse_arguments_split_dwarf() {
        let args = stringvec!["-gsplit-dwarf", "-c", "foo.cpp", "-o", "foo.o"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cpp"), input.to_str());
        assert_map_contains!(
            outputs,
            ("obj", PathBuf::from("foo.o")),
            ("dwo", PathBuf::from("foo.dwo"))
        );
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-gsplit-dwarf"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_linker_options() {
        let args = stringvec![
            // is basically the same as `-z deps`
            "-Wl,--unresolved-symbols=report-all",
            "-z",
            "call-nop=suffix-nop",
            "-z",
            "deps",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        ];

        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert_eq!(3, common_args.len());
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_coverage_outputs_gcno() {
        let args = stringvec!["--coverage", "-c", "foo.cpp", "-o", "foo.o"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            profile_generate,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cpp"), input.to_str());
        assert_map_contains!(
            outputs,
            ("obj", PathBuf::from("foo.o")),
            ("gcno", PathBuf::from("foo.gcno"))
        );
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["--coverage"], common_args);
        assert!(!msvc_show_includes);
        assert!(profile_generate);
    }

    #[test]
    fn test_parse_arguments_test_coverage_outputs_gcno() {
        let args = stringvec!["-ftest-coverage", "-c", "foo.cpp", "-o", "foo.o"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            profile_generate,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cpp"), input.to_str());
        assert_map_contains!(
            outputs,
            ("obj", PathBuf::from("foo.o")),
            ("gcno", PathBuf::from("foo.gcno"))
        );
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-ftest-coverage"], common_args);
        assert!(!msvc_show_includes);
        assert!(profile_generate);
    }

    #[test]
    fn test_parse_arguments_profile_generate() {
        let args = stringvec!["-fprofile-generate", "-c", "foo.cpp", "-o", "foo.o"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            profile_generate,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cpp"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-fprofile-generate"], common_args);
        assert!(!msvc_show_includes);
        assert!(profile_generate);
    }

    #[test]
    fn test_parse_arguments_extra() {
        let args = stringvec!["-c", "foo.cc", "-fabc", "-o", "foo.o", "-mxyz"];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cc"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-fabc", "-mxyz"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_values() {
        let args = stringvec![
            "-c", "foo.cxx", "-fabc", "-I", "include", "-o", "foo.o", "-include", "file"
        ];
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.cxx"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-Iinclude", "-include", "file"], preprocessor_args);
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_preprocessor_args() {
        let args = stringvec![
            "-c",
            "foo.c",
            "-fabc",
            "-MF",
            "file",
            "-o",
            "foo.o",
            "-MQ",
            "abc",
            "-nostdinc"
        ];
        let ParsedArguments {
            input,
            outputs,
            dependency_args,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-MF", "file"], dependency_args);
        assert_eq!(ovec!["-nostdinc"], preprocessor_args);
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_explicit_dep_target() {
        let args =
            stringvec!["-c", "foo.c", "-MT", "depfile", "-fabc", "-MF", "file", "-o", "foo.o"];
        let ParsedArguments {
            input,
            outputs,
            dependency_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-MF", "file"], dependency_args);
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_explicit_dep_target_needed() {
        let args = stringvec![
            "-c", "foo.c", "-MT", "depfile", "-fabc", "-MF", "file", "-o", "foo.o", "-MD"
        ];
        let ParsedArguments {
            input,
            outputs,
            dependency_args,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(
            ovec!["-MF", "file", "-MD", "-MT", "depfile"],
            dependency_args
        );
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_explicit_mq_dep_target_needed() {
        let args = stringvec![
            "-c", "foo.c", "-MQ", "depfile", "-fabc", "-MF", "file", "-o", "foo.o", "-MD"
        ];
        let ParsedArguments {
            input,
            outputs,
            dependency_args,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(
            ovec!["-MF", "file", "-MD", "-MQ", "depfile"],
            dependency_args
        );
        assert!(preprocessor_args.is_empty());
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_diagnostics_color() {
        fn get_color_mode(color_flag: &str) -> ColorMode {
            let args = stringvec!["-c", "foo.c", color_flag];
            match parse_arguments_(args) {
                CompilerArguments::Ok(args) => args.color_mode,
                o => panic!("Got unexpected parse result: {:?}", o),
            }
        }

        assert_eq!(get_color_mode("-fdiagnostics-color=always"), ColorMode::On);
        assert_eq!(get_color_mode("-fdiagnostics-color=never"), ColorMode::Off);
        assert_eq!(get_color_mode("-fdiagnostics-color=auto"), ColorMode::Auto);
        assert_eq!(get_color_mode("-fno-diagnostics-color"), ColorMode::Off);
        assert_eq!(get_color_mode("-fdiagnostics-color"), ColorMode::On);
    }

    #[test]
    fn color_mode_preprocess() {
        let args = stringvec!["-c", "foo.c", "-fdiagnostics-color"];
        let args = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };

        assert!(args.common_args.contains(&"-fdiagnostics-color".into()));
    }

    #[test]
    fn test_parse_arguments_dep_target_needed() {
        let args = stringvec!["-c", "foo.c", "-fabc", "-MF", "file", "-o", "foo.o", "-MD"];
        let ParsedArguments {
            input,
            outputs,
            dependency_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-MF", "file", "-MD", "-MT", "foo.o"], dependency_args);
        assert_eq!(ovec!["-fabc"], common_args);
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_parse_arguments_empty_args() {
        assert_eq!(CompilerArguments::NotCompilation, parse_arguments_(vec!()));
    }

    #[test]
    fn test_parse_arguments_not_compile() {
        assert_eq!(
            CompilerArguments::NotCompilation,
            parse_arguments_(stringvec!["-o", "foo"])
        );
    }

    #[test]
    fn test_parse_arguments_too_many_inputs() {
        assert_eq!(
            CompilerArguments::CannotCache("multiple input files", None),
            parse_arguments_(stringvec!["-c", "foo.c", "-o", "foo.o", "bar.c"])
        );
    }

    #[test]
    fn test_parse_arguments_link() {
        assert_eq!(
            CompilerArguments::NotCompilation,
            parse_arguments_(stringvec!["-shared", "foo.o", "-o", "foo.so", "bar.o"])
        );
    }

    #[test]
    fn test_parse_arguments_pgo() {
        assert_eq!(
            CompilerArguments::CannotCache("-fprofile-use", None),
            parse_arguments_(stringvec!["-c", "foo.c", "-fprofile-use", "-o", "foo.o"])
        );
        assert_eq!(
            CompilerArguments::CannotCache("-fprofile-use", None),
            parse_arguments_(stringvec![
                "-c",
                "foo.c",
                "-fprofile-use=file",
                "-o",
                "foo.o"
            ])
        );
    }

    #[test]
    fn test_parse_arguments_response_file() {
        assert_eq!(
            CompilerArguments::CannotCache("@", None),
            parse_arguments_(stringvec!["-c", "foo.c", "@foo", "-o", "foo.o"])
        );
        assert_eq!(
            CompilerArguments::CannotCache("@", None),
            parse_arguments_(stringvec!["-c", "foo.c", "-o", "@foo"])
        );
    }

    #[test]
    fn test_parse_arguments_multiple_arch() {
        match parse_arguments_(stringvec!["-arch", "arm64", "-o", "foo.o", "-c", "foo.cpp"]) {
            CompilerArguments::Ok(_) => {}
            o => panic!("Got unexpected parse result: {:?}", o),
        }

        match parse_arguments_(stringvec![
            "-arch", "arm64", "-arch", "arm64", "-o", "foo.o", "-c", "foo.cpp"
        ]) {
            CompilerArguments::Ok(_) => {}
            o => panic!("Got unexpected parse result: {:?}", o),
        }

        assert_eq!(
            CompilerArguments::CannotCache("multiple different -arch", None),
            parse_arguments_(stringvec![
                "-fPIC", "-arch", "arm64", "-arch", "i386", "-o", "foo.o", "-c", "foo.cpp"
            ])
        );
    }

    #[test]
    fn at_signs() {
        let td = tempfile::Builder::new()
            .prefix("sccache")
            .tempdir()
            .unwrap();
        File::create(td.path().join("foo"))
            .unwrap()
            .write_all(
                b"\
            -c foo.c -o foo.o\
        ",
            )
            .unwrap();
        let arg = format!("@{}", td.path().join("foo").display());
        let ParsedArguments {
            input,
            outputs,
            preprocessor_args,
            msvc_show_includes,
            common_args,
            ..
        } = match parse_arguments_(vec![arg]) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert!(preprocessor_args.is_empty());
        assert!(common_args.is_empty());
        assert!(!msvc_show_includes);
    }

    #[test]
    fn test_compile_simple() {
        let creator = new_creator();
        let f = TestFixture::new();
        let parsed_args = ParsedArguments {
            input: "foo.c".into(),
            #[cfg(feature = "dist-client")]
            dist_input: "foo.i".into(),
            compilation_flag: "-c".into(),
            depfile: None,
            outputs: vec![("obj", "foo.o".into())].into_iter().collect(),
            dependency_args: vec![],
            preprocessor_args: vec![],
            common_args: vec![],
            extra_hash_files: vec![],
            msvc_show_includes: false,
            profile_generate: false,
            color_mode: ColorMode::Auto,
        };
        let compiler = &f.bins[0];
        // Compiler invocation.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "", "")));
        let mut path_transformer = dist::PathTransformer::default();
        let (command, dist_command, cacheable) = generate_compile_commands(
            &mut path_transformer,
            compiler,
            &parsed_args,
            f.tempdir.path(),
            &[],
        )
        .unwrap();
        #[cfg(feature = "dist-client")]
        match dist_command {
            Some(cmd) => assert!(cmd.arguments.iter().any(|x| x == "foo.i")),
            None => unreachable!(),
        }
        #[cfg(not(feature = "dist-client"))]
        assert!(dist_command.is_none());
        let _ = command.execute(&creator).wait();
        assert_eq!(Cacheable::Yes, cacheable);
        // Ensure that we ran all processes.
        assert_eq!(0, creator.lock().unwrap().children.len());
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_parse_arguments_remote_rewrite_includes() {
        let args = stringvec![
            "-DX",
            "-UY",
            "-nostdinc",
            "-x",
            "c",
            "-c",
            "foo.c",
            "-o",
            "foo.o"
        ];
        let ParsedArguments {
            input,
            dist_input,
            outputs,
            preprocessor_args,
            compilation_flag,
            common_args,
            ..
        } = match parse_arguments_rewrite_include_(args) {
            CompilerArguments::Ok(args) => args,
            o => panic!("Got unexpected parse result: {:?}", o),
        };
        assert_eq!(Some("foo.c"), input.to_str());
        assert_eq!(Some("foo.c"), dist_input.to_str());
        assert_map_contains!(outputs, ("obj", PathBuf::from("foo.o")));
        assert_eq!(ovec!["-nostdinc"], preprocessor_args);
        assert_eq!(Some("-c -fpreprocessed"), compilation_flag.to_str());
        assert_eq!(ovec!["-DX", "-UY", "-xc", "-fdirectives-only"], common_args);
    }
}
