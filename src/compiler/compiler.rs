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

use crate::cache::{Cache, CacheWrite, DecompressionFailure, Storage};
use crate::compiler::c::{CCompiler, CCompilerKind};
use crate::compiler::clang::Clang;
use crate::compiler::diab::Diab;
use crate::compiler::gcc::Gcc;
use crate::compiler::msvc;
use crate::compiler::msvc::Msvc;
use crate::compiler::nvcc::Nvcc;
use crate::compiler::rust::{Rust, RustupProxy};
use crate::dist;
#[cfg(feature = "dist-client")]
use crate::dist::pkg;
use crate::lru_disk_cache;
use crate::mock_command::{exit_status, CommandChild, CommandCreatorSync, RunCommand};
use crate::protocol::Compile;
use crate::util::{fmt_duration_as_secs, ref_env, run_input_output};
use crate::util::{Digest, HashToDigest};
use filetime::FileTime;
use std::borrow::Cow;
use std::collections::HashMap;
use std::ffi::OsString;
use std::fmt;
#[cfg(feature = "dist-client")]
use std::fs;
use std::fs::File;
use std::future::Future;
use std::hash::Hash;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::process::{self, Stdio};
use std::str;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tempfile::TempDir;

use crate::errors::*;

/// Can dylibs (shared libraries or proc macros) be distributed on this platform?
#[cfg(all(feature = "dist-client", target_os = "linux", target_arch = "x86_64"))]
pub const CAN_DIST_DYLIBS: bool = true;
#[cfg(all(
    feature = "dist-client",
    not(all(target_os = "linux", target_arch = "x86_64"))
))]
pub const CAN_DIST_DYLIBS: bool = false;

#[derive(Clone, Debug)]
pub struct CompileCommand {
    pub executable: PathBuf,
    pub arguments: Vec<OsString>,
    pub env_vars: Vec<(OsString, OsString)>,
    pub cwd: PathBuf,
}

impl CompileCommand {
    pub async fn execute<T>(self, creator: &T) -> Result<process::Output>
    where
        T: CommandCreatorSync,
    {
        let mut cmd = creator.clone().new_command_sync(self.executable);
        cmd.args(&self.arguments)
            .env_clear()
            .envs(self.env_vars)
            .current_dir(self.cwd);
        run_input_output(cmd, None).await
    }
}

/// Supported compilers.
#[derive(Debug, PartialEq, Clone)]
pub enum CompilerKind {
    /// A C compiler.
    C(CCompilerKind),
    /// A Rust compiler.
    Rust,
}

impl CompilerKind {
    pub fn lang_kind(&self) -> String {
        match self {
            CompilerKind::C(CCompilerKind::Nvcc) => "CUDA",
            CompilerKind::C(_) => "C/C++",
            CompilerKind::Rust => "Rust",
        }
        .to_string()
    }
}

#[cfg(feature = "dist-client")]
pub type DistPackagers = (
    Box<dyn pkg::InputsPackager>,
    Box<dyn pkg::ToolchainPackager>,
    Box<dyn OutputsRewriter>,
);

enum CacheLookupResult {
    Success(CompileResult, process::Output),
    Miss(MissType),
}

/// An interface to a compiler for argument parsing.
pub trait Compiler<T>: Send + 'static
where
    T: CommandCreatorSync,
{
    /// Return the kind of compiler.
    fn kind(&self) -> CompilerKind;
    /// Retrieve a packager
    #[cfg(feature = "dist-client")]
    fn get_toolchain_packager(&self) -> Box<dyn pkg::ToolchainPackager>;
    /// Determine whether `arguments` are supported by this compiler.
    fn parse_arguments(
        &self,
        arguments: &[OsString],
        cwd: &Path,
        base_dir: Option<&PathBuf>,
        #[cfg(feature = "dist-client")] rewrite_includes_only: bool,
    ) -> CompilerArguments<Box<dyn CompilerHasher<T> + 'static>>;
    fn box_clone(&self) -> Box<dyn Compiler<T>>;
}

impl<T: CommandCreatorSync> Clone for Box<dyn Compiler<T>> {
    fn clone(&self) -> Box<dyn Compiler<T>> {
        self.box_clone()
    }
}

pub trait CompilerProxy<T>: Send + 'static
where
    T: CommandCreatorSync + Sized,
{
    /// Maps the executable to be used in `cwd` to the true, proxied compiler.
    ///
    /// Returns the absolute path to the true compiler and the timestamp of
    /// timestamp of the true compiler. Iff the resolution fails,
    /// the returned future resolves to an error with more information.
    fn resolve_proxied_executable(
        &self,
        creator: T,
        cwd: PathBuf,
        env_vars: &[(OsString, OsString)],
    ) -> Pin<Box<dyn Future<Output = Result<(PathBuf, FileTime)>> + Send + 'static>>;

    /// Create a clone of `Self` and puts it in a `Box`
    fn box_clone(&self) -> Box<dyn CompilerProxy<T>>;
}

impl<T: CommandCreatorSync> Clone for Box<dyn CompilerProxy<T>> {
    fn clone(&self) -> Box<dyn CompilerProxy<T>> {
        self.box_clone()
    }
}

/// An interface to a compiler for hash key generation, the result of
/// argument parsing.
#[async_trait]
pub trait CompilerHasher<T>: fmt::Debug + Send + 'static
where
    T: CommandCreatorSync,
{
    /// Given information about a compiler command, generate a hash key
    /// that can be used for cache lookups, as well as any additional
    /// information that can be reused for compilation if necessary.
    async fn generate_hash_key(
        self: Box<Self>,
        creator: &T,
        cwd: PathBuf,
        env_vars: Vec<(OsString, OsString)>,
        may_dist: bool,
        pool: &tokio::runtime::Handle,
    ) -> Result<HashResult>;

    /// Return the state of any `--color` option passed to the compiler.
    fn color_mode(&self) -> ColorMode;

    /// Look up a cached compile result in `storage`. If not found, run the
    /// compile and store the result.
    #[allow(clippy::too_many_arguments)]
    async fn get_cached_or_compile(
        self: Box<Self>,
        dist_client: Option<Arc<dyn dist::Client>>,
        creator: T,
        storage: Arc<dyn Storage>,
        arguments: Vec<OsString>,
        cwd: PathBuf,
        env_vars: Vec<(OsString, OsString)>,
        cache_control: CacheControl,
        pool: tokio::runtime::Handle,
    ) -> Result<(CompileResult, process::Output)> {
        let out_pretty = self.output_pretty().into_owned();
        debug!("[{}]: get_cached_or_compile: {:?}", out_pretty, arguments);
        let start = Instant::now();
        let may_dist = dist_client.is_some();
        let result = self
            .generate_hash_key(&creator, cwd.clone(), env_vars, may_dist, &pool)
            .await;
        debug!(
            "[{}]: generate_hash_key took {}",
            out_pretty,
            fmt_duration_as_secs(&start.elapsed())
        );
        let (key, compilation, weak_toolchain_key) = match result {
            Err(e) => {
                return match e.downcast::<ProcessError>() {
                    Ok(ProcessError(output)) => Ok((CompileResult::Error, output)),
                    Err(e) => Err(e),
                };
            }
            Ok(HashResult {
                key,
                compilation,
                weak_toolchain_key,
            }) => (key, compilation, weak_toolchain_key),
        };
        trace!("[{}]: Hash key: {}", out_pretty, key);
        // If `ForceRecache` is enabled, we won't check the cache.
        let start = Instant::now();
        let cache_status = async {
            if cache_control == CacheControl::ForceRecache {
                Ok(Cache::Recache)
            } else {
                storage.get(&key).await
                // TODO: if not found, and there is a remote shared storage,
                //       fetch from remote storage before doing the compilation.
            }
        };

        // Set a maximum time limit for the cache to respond before we forge
        // ahead ourselves with a compilation.
        let timeout = Duration::new(60, 0);
        let cache_status = tokio::time::timeout(timeout, cache_status);

        // Check the result of the cache lookup.
        let duration = start.elapsed();
        let outputs = compilation
            .outputs()
            .map(|(key, path)| (key.to_string(), cwd.join(path)))
            .collect::<HashMap<_, _>>();

        let lookup = match cache_status.await {
            Ok(Ok(Cache::Hit(mut entry))) => {
                debug!(
                    "[{}]: Cache hit in {}",
                    out_pretty,
                    fmt_duration_as_secs(&duration)
                );
                let stdout = entry.get_stdout();
                let stderr = entry.get_stderr();
                let output = process::Output {
                    status: exit_status(0),
                    stdout,
                    stderr,
                };
                let hit = CompileResult::CacheHit(duration);
                match entry.extract_objects(outputs.clone(), &pool).await {
                    Ok(()) => Ok(CacheLookupResult::Success(hit, output)),
                    Err(e) => {
                        if e.downcast_ref::<DecompressionFailure>().is_some() {
                            debug!("[{}]: Failed to decompress object", out_pretty);
                            Ok(CacheLookupResult::Miss(MissType::CacheReadError))
                        } else {
                            Err(e)
                        }
                    }
                }
            }
            Ok(Ok(Cache::Miss)) => {
                debug!(
                    "[{}]: Cache miss in {}",
                    out_pretty,
                    fmt_duration_as_secs(&duration)
                );
                Ok(CacheLookupResult::Miss(MissType::Normal))
            }
            Ok(Ok(Cache::Recache)) => {
                debug!(
                    "[{}]: Cache recache in {}",
                    out_pretty,
                    fmt_duration_as_secs(&duration)
                );
                Ok(CacheLookupResult::Miss(MissType::ForcedRecache))
            }
            Ok(Err(err)) => {
                error!("[{}]: Cache read error: {:?}", out_pretty, err);
                Ok(CacheLookupResult::Miss(MissType::CacheReadError))
            }
            Err(_elapsed) => {
                debug!(
                    "[{}]: Cache timed out {}",
                    out_pretty,
                    fmt_duration_as_secs(&duration)
                );
                Ok(CacheLookupResult::Miss(MissType::TimedOut))
            }
        }?;

        match lookup {
            CacheLookupResult::Success(compile_result, output) => {
                Ok::<_, Error>((compile_result, output))
            }
            CacheLookupResult::Miss(miss_type) => {
                // Cache miss, so compile it.
                let start = Instant::now();

                let (cacheable, dist_type, compiler_result) = dist_or_local_compile(
                    dist_client,
                    creator,
                    cwd,
                    compilation,
                    weak_toolchain_key,
                    out_pretty.clone(),
                )
                .await?;
                let duration = start.elapsed();
                // TODO: better scheduling with duration information. Avoid slow
                //       remote machine.
                if !compiler_result.status.success() {
                    debug!(
                        "[{}]: Compiled but failed, not storing in cache",
                        out_pretty
                    );
                    return Ok((CompileResult::CompileFailed, compiler_result));
                }
                if cacheable != Cacheable::Yes {
                    // Not cacheable
                    debug!("[{}]: Compiled but not cacheable", out_pretty);
                    return Ok((CompileResult::NotCacheable, compiler_result));
                }
                debug!(
                    "[{}]: Compiled in {}, storing in cache",
                    out_pretty,
                    fmt_duration_as_secs(&duration)
                );
                let mut entry = CacheWrite::from_objects(outputs, &pool)
                    .await
                    .context("failed to zip up compiler outputs")?;

                entry.put_stdout(&compiler_result.stdout)?;
                entry.put_stderr(&compiler_result.stderr)?;

                let out_pretty2 = out_pretty.clone();
                // Try to finish storing the newly-written cache
                // entry. We'll get the result back elsewhere.
                let future = async move {
                    match storage.put(&key, entry).await {
                        Ok(_) => debug!("[{}]: Stored in cache successfully!", out_pretty2),
                        Err(ref e) => debug!("[{}]: Cache write error: {:?}", out_pretty2, e),
                    }

                    Ok(CacheWriteInfo {
                        object_file_pretty: out_pretty2,
                        duration,
                    })
                };
                let future = Box::pin(future);
                Ok((
                    CompileResult::CacheMiss(miss_type, dist_type, duration, future),
                    compiler_result,
                ))
            }
        }
        .with_context(|| format!("failed to store `{}` to cache", out_pretty))
    }

    /// A descriptive string about the file that we're going to be producing.
    ///
    /// This is primarily intended for debug logging and such, not for actual
    /// artifact generation.
    fn output_pretty(&self) -> Cow<'_, str>;

    fn box_clone(&self) -> Box<dyn CompilerHasher<T>>;
}

#[cfg(not(feature = "dist-client"))]
async fn dist_or_local_compile<T>(
    _dist_client: Option<Arc<dyn dist::Client>>,
    creator: T,
    _cwd: PathBuf,
    compilation: Box<dyn Compilation>,
    _weak_toolchain_key: String,
    out_pretty: String,
) -> Result<(Cacheable, DistType, process::Output)>
where
    T: CommandCreatorSync,
{
    let mut path_transformer = dist::PathTransformer::default();
    let (compile_cmd, _dist_compile_cmd, cacheable) = compilation
        .generate_compile_commands(&mut path_transformer)
        .context("Failed to generate compile commands")?;

    debug!("[{}]: Compiling locally", out_pretty);
    compile_cmd
        .execute(&creator)
        .await
        .map(move |o| (cacheable, DistType::NoDist, o))
}

#[cfg(feature = "dist-client")]
async fn dist_or_local_compile<T>(
    dist_client: Option<Arc<dyn dist::Client>>,
    creator: T,
    cwd: PathBuf,
    compilation: Box<dyn Compilation>,
    weak_toolchain_key: String,
    out_pretty: String,
) -> Result<(Cacheable, DistType, process::Output)>
where
    T: CommandCreatorSync,
{
    use std::io;

    let mut path_transformer = dist::PathTransformer::default();
    let (compile_cmd, dist_compile_cmd, cacheable) = compilation
        .generate_compile_commands(&mut path_transformer)
        .context("Failed to generate compile commands")?;

    let dist_client = match dist_client {
        Some(dc) => dc,
        None => {
            debug!("[{}]: Compiling locally", out_pretty);
            return compile_cmd
                .execute(&creator)
                .await
                .map(move |o| (cacheable, DistType::NoDist, o));
        }
    };

    debug!("[{}]: Attempting distributed compilation", out_pretty);
    let out_pretty2 = out_pretty.clone();

    let local_executable = compile_cmd.executable.clone();
    let local_executable2 = compile_cmd.executable.clone();

    let do_dist_compile = async move {
        let mut dist_compile_cmd =
            dist_compile_cmd.context("Could not create distributed compile command")?;
        debug!("[{}]: Creating distributed compile request", out_pretty);
        let dist_output_paths = compilation
            .outputs()
            .map(|(_key, path)| path_transformer.as_dist_abs(&cwd.join(path)))
            .collect::<Option<_>>()
            .context("Failed to adapt an output path for distributed compile")?;
        let (inputs_packager, toolchain_packager, outputs_rewriter) =
            compilation.into_dist_packagers(path_transformer)?;

        debug!(
            "[{}]: Identifying dist toolchain for {:?}",
            out_pretty, local_executable
        );
        let (dist_toolchain, maybe_dist_compile_executable) = dist_client
            .put_toolchain(local_executable, weak_toolchain_key, toolchain_packager)
            .await?;
        let mut tc_archive = None;
        if let Some((dist_compile_executable, archive_path)) = maybe_dist_compile_executable {
            dist_compile_cmd.executable = dist_compile_executable;
            tc_archive = Some(archive_path);
        }

        debug!("[{}]: Requesting allocation", out_pretty);
        let jares = dist_client.do_alloc_job(dist_toolchain.clone()).await?;
        let job_alloc = match jares {
            dist::AllocJobResult::Success {
                job_alloc,
                need_toolchain: true,
            } => {
                debug!(
                    "[{}]: Sending toolchain {} for job {}",
                    out_pretty, dist_toolchain.archive_id, job_alloc.job_id
                );

                match dist_client
                    .do_submit_toolchain(job_alloc.clone(), dist_toolchain)
                    .await
                    .map_err(|e| e.context("Could not submit toolchain"))?
                {
                    dist::SubmitToolchainResult::Success => Ok(job_alloc),
                    dist::SubmitToolchainResult::JobNotFound => {
                        bail!("Job {} not found on server", job_alloc.job_id)
                    }
                    dist::SubmitToolchainResult::CannotCache => bail!(
                        "Toolchain for job {} could not be cached by server",
                        job_alloc.job_id
                    ),
                }
            }
            dist::AllocJobResult::Success {
                job_alloc,
                need_toolchain: false,
            } => Ok(job_alloc),
            dist::AllocJobResult::Fail { msg } => {
                debug!("Failed to allocate job");
                Err(anyhow!("Failed to allocate job").context(msg))
            }
        }?;
        let job_id = job_alloc.job_id;
        let server_id = job_alloc.server_id;
        debug!("[{}]: Running job", out_pretty);
        let ((job_id, server_id), (jres, path_transformer)) = dist_client
            .do_run_job(
                job_alloc,
                dist_compile_cmd,
                dist_output_paths,
                inputs_packager,
            )
            .await
            .map(move |res| ((job_id, server_id), res))
            .with_context(|| {
                format!(
                    "could not run distributed compilation job on {:?}",
                    server_id
                )
            })?;

        let jc = match jres {
            dist::RunJobResult::Complete(jc) => jc,
            dist::RunJobResult::JobNotFound => bail!("Job {} not found on server", job_id),
        };
        info!(
            "fetched {:?}",
            jc.outputs
                .iter()
                .map(|&(ref p, ref bs)| (p, bs.lens().to_string()))
                .collect::<Vec<_>>()
        );
        let mut output_paths: Vec<PathBuf> = vec![];
        macro_rules! try_or_cleanup {
            ($v:expr) => {{
                match $v {
                    Ok(v) => v,
                    Err(e) => {
                        // Do our best to clear up. We may end up deleting a file that we just wrote over
                        // the top of, but it's better to clear up too much than too little
                        for local_path in output_paths.iter() {
                            if let Err(e) = fs::remove_file(local_path) {
                                if e.kind() != io::ErrorKind::NotFound {
                                    warn!("{} while attempting to clear up {}", e, local_path.display())
                                }
                            }
                        }
                        return Err(e)
                    },
                }
            }};
        }

        for (path, output_data) in jc.outputs {
            let len = output_data.lens().actual;
            let local_path = try_or_cleanup!(path_transformer
                .to_local(&path)
                .with_context(|| format!("unable to transform output path {}", path)));
            output_paths.push(local_path);
            // Do this first so cleanup works correctly
            let local_path = output_paths.last().expect("nothing in vec after push");

            let mut file = try_or_cleanup!(File::create(&local_path)
                .with_context(|| format!("Failed to create output file {}", local_path.display())));
            let count = try_or_cleanup!(io::copy(&mut output_data.into_reader(), &mut file)
                .with_context(|| format!("Failed to write output to {}", local_path.display())));

            assert!(count == len);
        }
        let extra_inputs = match tc_archive {
            Some(p) => vec![p],
            None => vec![],
        };
        try_or_cleanup!(outputs_rewriter
            .handle_outputs(&path_transformer, &output_paths, &extra_inputs)
            .with_context(|| "failed to rewrite outputs from compile"));
        Ok((DistType::Ok(server_id), jc.output.into()))
    };

    use futures::TryFutureExt;
    do_dist_compile
        .or_else(move |e| async move {
            if let Some(HttpClientError(_)) = e.downcast_ref::<HttpClientError>() {
                Err(e)
            } else if let Some(lru_disk_cache::Error::FileTooLarge) =
                e.downcast_ref::<lru_disk_cache::Error>()
            {
                Err(anyhow!(
                    "Could not cache dist toolchain for {:?} locally.
                 Increase `toolchain_cache_size` or decrease the toolchain archive size.",
                    local_executable2
                ))
            } else {
                // `{:#}` prints the error and the causes in a single line.
                let errmsg = format!("{:#}", e);
                warn!(
                    "[{}]: Could not perform distributed compile, falling back to local: {}",
                    out_pretty2, errmsg
                );

                compile_cmd
                    .execute(&creator)
                    .await
                    .map(|o| (DistType::Error, o))
            }
        })
        .map_ok(move |(dt, o)| (cacheable, dt, o))
        .await
}

impl<T: CommandCreatorSync> Clone for Box<dyn CompilerHasher<T>> {
    fn clone(&self) -> Box<dyn CompilerHasher<T>> {
        self.box_clone()
    }
}

/// An interface to a compiler for actually invoking compilation.
pub trait Compilation: Send {
    /// Given information about a compiler command, generate a command that can
    /// execute the compiler.
    fn generate_compile_commands(
        &self,
        path_transformer: &mut dist::PathTransformer,
    ) -> Result<(CompileCommand, Option<dist::CompileCommand>, Cacheable)>;

    /// Create a function that will create the inputs used to perform a distributed compilation
    #[cfg(feature = "dist-client")]
    fn into_dist_packagers(
        self: Box<Self>,
        _path_transformer: dist::PathTransformer,
    ) -> Result<DistPackagers>;

    /// Returns an iterator over the results of this compilation.
    ///
    /// Each item is a descriptive (and unique) name of the output paired with
    /// the path where it'll show up.
    fn outputs<'a>(&'a self) -> Box<dyn Iterator<Item = (&'a str, &'a Path)> + 'a>;
}

#[cfg(feature = "dist-client")]
pub trait OutputsRewriter: Send {
    /// Perform any post-compilation handling of outputs, given a Vec of the dist_path and local_path
    fn handle_outputs(
        self: Box<Self>,
        path_transformer: &dist::PathTransformer,
        output_paths: &[PathBuf],
        extra_inputs: &[PathBuf],
    ) -> Result<()>;
}

#[cfg(feature = "dist-client")]
pub struct NoopOutputsRewriter;
#[cfg(feature = "dist-client")]
impl OutputsRewriter for NoopOutputsRewriter {
    fn handle_outputs(
        self: Box<Self>,
        _path_transformer: &dist::PathTransformer,
        _output_paths: &[PathBuf],
        _extra_inputs: &[PathBuf],
    ) -> Result<()> {
        Ok(())
    }
}

/// Result of generating a hash from a compiler command.
pub struct HashResult {
    /// The hash key of the inputs.
    pub key: String,
    /// An object to use for the actual compilation, if necessary.
    pub compilation: Box<dyn Compilation + 'static>,
    /// A weak key that may be used to identify the toolchain
    pub weak_toolchain_key: String,
}

/// Possible results of parsing compiler arguments.
#[derive(Debug, PartialEq)]
pub enum CompilerArguments<T> {
    /// Commandline can be handled.
    Ok(T),
    /// Cannot cache this compilation.
    CannotCache(&'static str, Option<String>),
    /// This commandline is not a compile.
    NotCompilation,
}

macro_rules! cannot_cache {
    ($why:expr) => {
        return CompilerArguments::CannotCache($why, None)
    };
    ($why:expr, $extra_info:expr) => {
        return CompilerArguments::CannotCache($why, Some($extra_info))
    };
}

macro_rules! try_or_cannot_cache {
    ($arg:expr, $why:expr) => {{
        match $arg {
            Ok(arg) => arg,
            Err(e) => cannot_cache!($why, e.to_string()),
        }
    }};
}

macro_rules! try_string_arg {
    ($e:expr) => {
        match $e {
            Ok(s) => s,
            Err(e) => {
                debug!("basedir transform fail: {}", e);
                cannot_cache!("basedir transform fail");
            }
        }
    };
}

/// Specifics about distributed compilation.
#[derive(Debug, PartialEq)]
pub enum DistType {
    /// Distribution was not enabled.
    NoDist,
    /// Distributed compile success.
    Ok(dist::ServerId),
    /// Distributed compile failed.
    Error,
}

/// Specifics about cache misses.
#[derive(Debug, PartialEq)]
pub enum MissType {
    /// The compilation was not found in the cache, nothing more.
    Normal,
    /// Cache lookup was overridden, recompilation was forced.
    ForcedRecache,
    /// Cache took too long to respond.
    TimedOut,
    /// Error reading from cache
    CacheReadError,
}

/// Information about a successful cache write.
pub struct CacheWriteInfo {
    pub object_file_pretty: String,
    pub duration: Duration,
}

/// The result of a compilation or cache retrieval.
pub enum CompileResult {
    /// An error made the compilation not possible.
    Error,
    /// Result was found in cache.
    CacheHit(Duration),
    /// Result was not found in cache.
    ///
    /// The `CacheWriteFuture` will resolve when the result is finished
    /// being stored in the cache.
    CacheMiss(
        MissType,
        DistType,
        Duration,
        Pin<Box<dyn Future<Output = Result<CacheWriteInfo>> + Send>>,
    ),
    /// Not in cache, but the compilation result was determined to be not cacheable.
    NotCacheable,
    /// Not in cache, but compilation failed.
    CompileFailed,
}

/// The state of `--color` options passed to a compiler.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub enum ColorMode {
    Off,
    On,
    Auto,
}

impl Default for ColorMode {
    fn default() -> ColorMode {
        ColorMode::Auto
    }
}

/// Can't derive(Debug) because of `CacheWriteFuture`.
impl fmt::Debug for CompileResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            CompileResult::Error => write!(f, "CompileResult::Error"),
            CompileResult::CacheHit(ref d) => write!(f, "CompileResult::CacheHit({:?})", d),
            CompileResult::CacheMiss(ref m, ref dt, ref d, _) => {
                write!(f, "CompileResult::CacheMiss({:?}, {:?}, {:?}, _)", d, m, dt)
            }
            CompileResult::NotCacheable => write!(f, "CompileResult::NotCacheable"),
            CompileResult::CompileFailed => write!(f, "CompileResult::CompileFailed"),
        }
    }
}

/// Can't use derive(PartialEq) because of the `CacheWriteFuture`.
impl PartialEq<CompileResult> for CompileResult {
    fn eq(&self, other: &CompileResult) -> bool {
        match (self, other) {
            (&CompileResult::Error, &CompileResult::Error) => true,
            (&CompileResult::CacheHit(_), &CompileResult::CacheHit(_)) => true,
            (
                &CompileResult::CacheMiss(ref m, ref dt, _, _),
                &CompileResult::CacheMiss(ref n, ref dt2, _, _),
            ) => m == n && dt == dt2,
            (&CompileResult::NotCacheable, &CompileResult::NotCacheable) => true,
            (&CompileResult::CompileFailed, &CompileResult::CompileFailed) => true,
            _ => false,
        }
    }
}

/// Can this result be stored in cache?
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Cacheable {
    Yes,
    No,
}

/// Control of caching behavior.
#[derive(Debug, PartialEq)]
pub enum CacheControl {
    /// Default caching behavior.
    Default,
    /// Ignore existing cache entries, force recompilation.
    ForceRecache,
}

/// Creates a future that will write `contents` to `path` inside of a temporary
/// directory.
///
/// The future will resolve to the temporary directory and an absolute path
/// inside that temporary directory with a file that has the same filename as
/// `path` contains the `contents` specified.
///
/// Note that when the `TempDir` is dropped it will delete all of its contents
/// including the path returned.
pub async fn write_temp_file(
    pool: &tokio::runtime::Handle,
    path: &Path,
    contents: Vec<u8>,
) -> Result<(TempDir, PathBuf)> {
    let path = path.to_owned();
    pool.spawn_blocking(move || {
        let dir = tempfile::Builder::new().prefix("sccache").tempdir()?;
        let src = dir.path().join(path);
        let mut file = File::create(&src)?;
        file.write_all(&contents)?;
        Ok::<_, anyhow::Error>((dir, src))
    })
    .await?
    .context("failed to write temporary file")
}

/// If `executable` is a known compiler, return `Some(Box<Compiler>)`.
async fn detect_compiler<T>(
    creator: T,
    compile: &Compile,
    pool: &tokio::runtime::Handle,
    dist_archive: Option<PathBuf>,
) -> Result<(Box<dyn Compiler<T>>, Option<Box<dyn CompilerProxy<T>>>)>
where
    T: CommandCreatorSync,
{
    let executable = PathBuf::from(&compile.exe);

    trace!("detect_compiler: {}", executable.display());

    // First, see if this looks like rustc.
    let filename = match executable.file_stem() {
        None => bail!("could not determine compiler kind"),
        Some(f) => f,
    };
    let filename = filename.to_string_lossy().to_lowercase();

    let rustc_vv = if filename == "rustc" || filename == "clippy-driver" {
        // Sanity check that it's really rustc.
        let mut child = creator.clone().new_command_sync(&executable);
        child
            .env_clear()
            .envs(ref_env(&compile.env_vars))
            .args(&["-vV"]);

        run_input_output(child, None).await.map(|output| {
            if let Ok(stdout) = String::from_utf8(output.stdout.clone()) {
                if stdout.starts_with("rustc ") {
                    return Some(Ok(stdout));
                }
            }
            Some(Err(ProcessError(output)))
        })?
    } else {
        None
    };

    let creator1 = creator.clone();
    let pool = pool.clone();
    let executable2 = executable.clone();
    match rustc_vv {
        Some(Ok(rustc_verbose_version)) => {
            debug!("Found rustc");

            let proxy = RustupProxy::find_proxy_executable::<T>(
                &executable2,
                "rustup",
                creator.clone(),
                &compile.env_vars,
            );
            use futures::TryFutureExt;
            let res = proxy.and_then(move |proxy| async move {
                match proxy {
                    Ok(Some(proxy)) => {
                        trace!("Found rustup proxy executable");
                        // take the pathbuf for rustc as resolved by the proxy
                        match proxy
                            .resolve_proxied_executable(
                                creator1,
                                PathBuf::from(&compile.cwd),
                                &compile.env_vars,
                            )
                            .await
                        {
                            Ok((resolved_path, _time)) => {
                                trace!("Resolved path with rustup proxy {:?}", &resolved_path);
                                Ok((Some(proxy), resolved_path))
                            }
                            Err(e) => {
                                trace!("Could not resolve compiler with rustup proxy: {}", e);
                                Ok((None, executable))
                            }
                        }
                    }
                    Ok(None) => {
                        trace!("Did not find rustup");
                        Ok((None, executable))
                    }
                    Err(e) => {
                        trace!("Did not find rustup due to {}, compiling without proxy", e);
                        Ok((None, executable))
                    }
                }
            });

            let (proxy, resolved_rustc) = res
                .await
                .map(|(proxy, resolved_compiler_executable)| {
                    (
                        proxy
                            .map(Box::new)
                            .map(|x: Box<RustupProxy>| x as Box<dyn CompilerProxy<T>>),
                        resolved_compiler_executable,
                    )
                })
                .unwrap_or_else(|_e| {
                    trace!("Compiling rust without proxy");
                    (None, executable2)
                });

            Rust::new(
                creator,
                resolved_rustc,
                &compile.env_vars,
                &rustc_verbose_version,
                dist_archive,
                pool,
            )
            .await
            .map(|c| {
                (
                    Box::new(c) as Box<dyn Compiler<T>>,
                    proxy as Option<Box<dyn CompilerProxy<T>>>,
                )
            })
        }
        Some(Err(e)) => Err(e).context("Failed to launch subprocess for compiler determination"),
        None => {
            let cc = detect_c_compiler(creator, compile, pool).await;
            cc.map(|c| (c, None))
        }
    }
}

async fn detect_c_compiler<T>(
    creator: T,
    compile: &Compile,
    pool: tokio::runtime::Handle,
) -> Result<Box<dyn Compiler<T>>>
where
    T: CommandCreatorSync,
{
    // Handle SCCACHE_COMPILERTYPE
    let mut ccompiler_type = match compile
        .env_vars
        .iter()
        .find(|(k, _)| k == "SCCACHE_COMPILERTYPE")
    {
        Some(k) => {
            let mut kind = String::from(k.1.to_str().unwrap());
            kind.make_ascii_lowercase();
            if !["gcc", "clang", "diab", "msvc", "clang-cl", "nvcc", "auto"]
                .contains(&kind.as_str())
            {
                bail!("unsupported c compiler type")
            }
            kind
        }
        None => String::from("auto"),
    };

    // Handle SCCACHE_COMPILERCHECK
    let mut ccompiler_check = match compile
        .env_vars
        .iter()
        .find(|(k, _)| k == "SCCACHE_COMPILERCHECK")
    {
        Some(c) => {
            let mut check = String::from(c.1.to_str().unwrap());
            check.make_ascii_lowercase();
            if !["content", "mtime", "version", "none"].contains(&check.as_str())
                && !check.starts_with("string:")
            {
                bail!("unsupported c compiler check type")
            }
            check
        }
        None => String::from("mtime"),
    };

    let executable = PathBuf::from(&compile.exe);

    if ccompiler_type == "auto" || ccompiler_check == "version" {
        trace!("detect_c_compiler");

        // NVCC needs to be first as msvc, clang, or gcc could
        // be the underlying host compiler for nvcc
        // Both clang and clang-cl define _MSC_VER on Windows, so we first
        // check for MSVC, then check whether _MT is defined, which is the
        // difference between clang and clang-cl.
        let test = b"#if defined(__NVCC__)
    nvcc
    #elif defined(_MSC_VER) && !defined(__clang__)
    msvc
    #elif defined(_MSC_VER) && defined(_MT)
    clang-cl
    #elif defined(__clang__)
    clang
    #elif defined(__GNUC__)
    gcc
    #elif defined(__DCC__)
    diab
    #else
    unknown
    #endif
    __VERSION__
    "
        .to_vec();
        // TODO: use pipe.
        let (tempdir, src) = write_temp_file(&pool, "testfile.c".as_ref(), test).await?;

        let mut cmd = creator.clone().new_command_sync(&executable);
        cmd.stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .envs(ref_env(&compile.env_vars));

        // Handle `gcc -B` since it decides compiler version.
        let mut cmd_args = vec!["-E"];
        if compile.exe.to_str().unwrap().contains("gcc")
            || compile.exe.to_str().unwrap().contains("g++")
        {
            if let Some(index) = compile
                .args
                .iter()
                .position(|x| x.to_string_lossy().starts_with("-B"))
            {
                cmd_args.push(compile.args[index].to_str().unwrap());
                if compile.args[index] == "-B" && index + 1 < compile.args.len() {
                    cmd_args.push(compile.args[index + 1].to_str().unwrap());
                }
            }
        }
        cmd.args(&cmd_args).arg(src);
        trace!("compiler {:?}", cmd);
        let child = cmd.spawn().await?;
        let output = child
            .wait_with_output()
            .await
            .context("failed to read child output")?;
        drop(tempdir);

        let stdout = match str::from_utf8(&output.stdout) {
            Ok(s) => s,
            Err(_) => bail!("Failed to parse output"),
        };
        let mut lines = stdout.lines().filter_map(|line| {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                None
            } else {
                Some(line)
            }
        });

        if let Some(kind) = lines.next() {
            if ccompiler_type == "auto" {
                ccompiler_type = kind.into();
            }

            if ccompiler_check == "version" {
                if let Some(version) = lines
                    .next()
                    // In case the compiler didn't expand the macro.
                    .filter(|&line| line != "__VERSION__")
                    .map(str::to_owned)
                {
                    ccompiler_check = String::from("string:") + version.as_str();
                }
            }
        }

        if ccompiler_type == "auto" || ccompiler_check == "version" {
            let stderr = String::from_utf8_lossy(&output.stderr);
            debug!("nothing useful in detection output {:?}", stdout);
            debug!("compiler status: {}", output.status);
            debug!("compiler stderr:\n{}", stderr);
            bail!(stderr.into_owned());
        }
    }

    let executable_digest = match ccompiler_check.as_str() {
        "none" => String::new(),
        "content" => {
            let mut m = Digest::new();
            let digest = Digest::file(executable.clone(), &pool).await?;
            m.update(digest.as_bytes());
            m.update(executable.to_string_lossy().as_bytes());
            m.finish()
        }
        "mtime" => {
            // mtime + size + executable name.
            let mut m = Digest::new();
            // metadata() will traverse symbolic links to query information
            // about the destination file
            let exe_md = executable.metadata()?;
            exe_md
                .modified()?
                .hash(&mut HashToDigest { digest: &mut m });
            m.update(&exe_md.len().to_ne_bytes());
            m.update(executable.to_string_lossy().as_bytes());
            m.finish()
        }
        x if x.starts_with("string:") => {
            // version + executable name.
            let mut m = Digest::new();
            m.update(x["string:".len()..].as_bytes());
            m.update(executable.to_string_lossy().as_bytes());
            m.finish()
        }
        _ => bail!("unknow compiler check"),
    };

    match ccompiler_type.as_str() {
        "clang" => {
            debug!("Found {}", ccompiler_type);
            return CCompiler::new(Clang, executable, executable_digest)
                .await
                .map(|c| Box::new(c) as Box<dyn Compiler<T>>);
        }
        "diab" => {
            debug!("Found diab");
            return CCompiler::new(Diab, executable, executable_digest)
                .await
                .map(|c| Box::new(c) as Box<dyn Compiler<T>>);
        }
        "gcc" => {
            debug!("Found {}", ccompiler_type);
            return CCompiler::new(Gcc, executable, executable_digest)
                .await
                .map(|c| Box::new(c) as Box<dyn Compiler<T>>);
        }
        "msvc" | "clang-cl" => {
            let is_clang = ccompiler_type == "clang-cl";
            debug!("Found MSVC (is clang: {})", is_clang);
            let prefix = msvc::detect_showincludes_prefix(
                &creator,
                executable.as_ref(),
                is_clang,
                &compile.env_vars,
                &pool,
            )
            .await?;
            trace!("showIncludes prefix: '{}'", prefix);

            return CCompiler::new(
                Msvc {
                    includes_prefix: prefix,
                    is_clang,
                },
                executable,
                executable_digest,
            )
            .await
            .map(|c| Box::new(c) as Box<dyn Compiler<T>>);
        }
        "nvcc" => {
            debug!("Found NVCC");
            return CCompiler::new(Nvcc, executable, executable_digest)
                .await
                .map(|c| Box::new(c) as Box<dyn Compiler<T>>);
        }
        _ => bail!("unknow compiler type"),
    }
}

/// If `executable` is a known compiler, return a `Box<Compiler>` containing information about it.
pub async fn get_compiler_info<T>(
    creator: T,
    compile: &Compile,
    pool: &tokio::runtime::Handle,
    dist_archive: Option<PathBuf>,
) -> Result<(Box<dyn Compiler<T>>, Option<Box<dyn CompilerProxy<T>>>)>
where
    T: CommandCreatorSync,
{
    let pool = pool.clone();
    detect_compiler(creator, compile, &pool, dist_archive).await
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cache::disk::DiskCache;
    use crate::mock_command::*;
    use crate::test::mock_storage::MockStorage;
    use crate::test::utils::*;
    use std::fs::{self, File};
    use std::io::Write;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;
    use std::u64;
    use tokio::runtime::Runtime;

    fn create_compile(f: &TestFixture) -> Compile {
        Compile {
            exe: OsString::from(&f.bins[0]),
            cwd: OsString::from(f.tempdir.path()),
            args: Vec::new(),
            env_vars: Vec::new(),
        }
    }

    fn get_hash_key(output: &Option<&str>, compile: &Compile) -> String {
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];

        if output.is_some() {
            next_command(
                &creator,
                Ok(MockChild::new(exit_status(0), output.unwrap(), "")),
            );
        }
        let c = detect_compiler(creator.clone(), compile, pool, None)
            .wait()
            .unwrap()
            .0;
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        hasher
            .generate_hash_key(
                &creator,
                PathBuf::from(compile.cwd.clone()),
                vec![],
                false,
                pool,
            )
            .wait()
            .unwrap()
            .key
    }

    fn get_mtime(exe: &Path) -> FileTime {
        let md = exe.metadata().unwrap();
        FileTime::from_last_modification_time(&md)
    }

    #[test]
    fn test_detect_compiler_kind_gcc() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(0), "\n\ngcc", "")));
        let c = detect_compiler(creator, &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Gcc), c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_gcc_dash_b() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command_with_args(
            &creator,
            Ok(MockChild::new(exit_status(0), "\n\ngcc", "")),
            |args| assert_eq!(ovec!["-E", "-B/a"].as_slice(), &args[..2]),
        );

        let c = detect_compiler(
            creator.clone(),
            &Compile {
                exe: OsString::from(f.mk_bin("xgcc").unwrap()),
                cwd: OsString::from(f.tempdir.path()),
                args: ovec!["-any", "-B/a", "-c", "foo.c"],
                env_vars: Vec::new(),
            },
            pool,
            None,
        )
        .wait()
        .unwrap()
        .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Gcc), c.kind());

        next_command_with_args(
            &creator,
            Ok(MockChild::new(exit_status(0), "\n\ngcc", "")),
            |args| assert!(args.iter().all(|x| !x.to_string_lossy().starts_with("-B"))),
        );

        let c = detect_compiler(
            creator.clone(),
            &Compile {
                exe: OsString::from(f.mk_bin("gcc").unwrap()),
                cwd: OsString::from(f.tempdir.path()),
                args: ovec!["-c", "foo.c"],
                env_vars: Vec::new(),
            },
            pool,
            None,
        )
        .wait()
        .unwrap()
        .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Gcc), c.kind());

        next_command_with_args(
            &creator,
            Ok(MockChild::new(exit_status(0), "\n\nclang", "")),
            |args| assert!(args.iter().all(|x| !x.to_string_lossy().starts_with("-B"))),
        );

        let c = detect_compiler(
            creator,
            &Compile {
                exe: OsString::from(f.mk_bin("clang").unwrap()),
                cwd: OsString::from(f.tempdir.path()),
                args: ovec!["-B/a", "-c", "foo.c"],
                env_vars: Vec::new(),
            },
            pool,
            None,
        )
        .wait()
        .unwrap()
        .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Clang), c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_clang() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(0), "clang\n", "")));
        let c = detect_compiler(creator, &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Clang), c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_msvc() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        let f = TestFixture::new();
        let srcfile = f.touch("test.h").unwrap();
        let mut s = srcfile.to_str().unwrap();
        if s.starts_with("\\\\?\\") {
            s = &s[4..];
        }
        let prefix = String::from("blah: ");
        let stdout = format!("{}{}\r\n", prefix, s);
        // Compiler detection output
        next_command(&creator, Ok(MockChild::new(exit_status(0), "\nmsvc\n", "")));
        // showincludes prefix detection output
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), &stdout, &String::new())),
        );
        let c = detect_compiler(creator.clone(), &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Msvc), c.kind());

        let compilers = [
            ("msvc", CCompilerKind::Msvc),
            ("clang-cl", CCompilerKind::Msvc),
        ];
        for (s, k) in &compilers {
            next_command(
                &creator,
                Ok(MockChild::new(exit_status(0), &stdout, &String::new())),
            );
            let c = detect_compiler(
                creator.clone(),
                &Compile {
                    exe: OsString::from(&f.bins[0]),
                    cwd: OsString::from(f.tempdir.path()),
                    args: Vec::new(),
                    env_vars: vec![(OsString::from("SCCACHE_COMPILERTYPE"), OsString::from(s))],
                },
                pool,
                None,
            )
            .wait()
            .unwrap()
            .0;
            assert_eq!(CompilerKind::C(k.clone()), c.kind());
        }
    }

    #[test]
    fn test_detect_compiler_kind_nvcc() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(0), "nvcc\n", "")));
        let c = detect_compiler(creator, &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Nvcc), c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_rustc() {
        let f = TestFixture::new();
        // Windows uses bin, everything else uses lib. Just create both.
        fs::create_dir(f.tempdir.path().join("lib")).unwrap();
        fs::create_dir(f.tempdir.path().join("bin")).unwrap();
        let rustc = f.mk_bin("rustc").unwrap();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        // rustc --vV
        next_command(
            &creator,
            Ok(MockChild::new(
                exit_status(0),
                "\
rustc 1.27.0 (3eda71b00 2018-06-19)
binary: rustc
commit-hash: 3eda71b00ad48d7bf4eef4c443e7f611fd061418
commit-date: 2018-06-19
host: x86_64-unknown-linux-gnu
release: 1.27.0
LLVM version: 6.0",
                "",
            )),
        );
        // rustc --print=sysroot
        let sysroot = f.tempdir.path().to_str().unwrap();
        next_command(&creator, Ok(MockChild::new(exit_status(0), &sysroot, "")));
        next_command(&creator, Ok(MockChild::new(exit_status(0), &sysroot, "")));
        next_command(&creator, Ok(MockChild::new(exit_status(0), &sysroot, "")));
        let c = detect_compiler(
            creator,
            &Compile {
                exe: OsString::from(rustc),
                cwd: OsString::from(f.tempdir.path()),
                args: Vec::new(),
                env_vars: Vec::new(),
            },
            pool,
            None,
        )
        .wait()
        .unwrap()
        .0;
        assert_eq!(CompilerKind::Rust, c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_diab() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(0), "\ndiab\n", "")));
        let c = detect_compiler(creator, &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        assert_eq!(CompilerKind::C(CCompilerKind::Diab), c.kind());
    }

    #[test]
    fn test_detect_compiler_kind_unknown() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "something", "")),
        );
        assert!(detect_compiler(
            creator,
            &Compile {
                exe: OsString::from("/foo/bar"),
                cwd: OsString::from(f.tempdir.path()),
                args: Vec::new(),
                env_vars: Vec::new(),
            },
            pool,
            None
        )
        .wait()
        .is_err());
    }

    #[test]
    fn test_detect_compiler_kind_process_fail() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(1), "", "")));
        assert!(detect_compiler(
            creator,
            &Compile {
                exe: OsString::from("/foo/bar"),
                cwd: OsString::from(f.tempdir.path()),
                args: Vec::new(),
                env_vars: Vec::new(),
            },
            pool,
            None
        )
        .wait()
        .is_err());
    }

    #[test]
    fn test_detect_compiler_kind_env_var() {
        let f = TestFixture::new();
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        let compilers = [
            ("gcc", CCompilerKind::Gcc),
            ("clang", CCompilerKind::Clang),
            ("nvcc", CCompilerKind::Nvcc),
            ("diab", CCompilerKind::Diab),
        ];

        for (s, k) in &compilers {
            let c = detect_compiler(
                creator.clone(),
                &Compile {
                    exe: OsString::from(&f.bins[0]),
                    cwd: OsString::from(f.tempdir.path()),
                    args: Vec::new(),
                    env_vars: vec![(OsString::from("SCCACHE_COMPILERTYPE"), OsString::from(s))],
                },
                pool,
                None,
            )
            .wait()
            .unwrap()
            .0;
            assert_eq!(CompilerKind::C(k.clone()), c.kind());
        }
    }

    #[test]
    fn test_compiler_check_none() {
        let f = TestFixture::new();
        let cwd = OsString::from(f.tempdir.path());
        let env_vars = vec![(
            OsString::from("SCCACHE_COMPILERCHECK"),
            OsString::from("none"),
        )];
        let gcc = f
            .mk_bin_contents("gcc", |mut f| {
                f.write_all("1".as_bytes())?;
                Ok(())
            })
            .unwrap();
        let clang = f
            .mk_bin_contents("clang", |mut f| {
                f.write_all("2".as_bytes())?;
                Ok(())
            })
            .unwrap();

        let key1 = get_hash_key(
            &Some("gcc\n\"11.0.0\""),
            &Compile {
                exe: OsString::from(&gcc),
                cwd: cwd.clone(),
                args: Vec::new(),
                env_vars: env_vars.clone(),
            },
        );

        thread::sleep(Duration::from_millis(50));

        let key2 = get_hash_key(
            &Some("clang\n\"12.0.0\""),
            &Compile {
                exe: OsString::from(&clang),
                cwd,
                args: Vec::new(),
                env_vars,
            },
        );

        assert_eq!(key1, key2);
    }

    #[test]
    fn test_compiler_check_mtime() {
        let f = TestFixture::new();
        let cwd = OsString::from(f.tempdir.path());
        let env_vars = vec![(
            OsString::from("SCCACHE_COMPILERCHECK"),
            OsString::from("mtime"),
        )];
        let gcc = f.mk_bin("gcc").unwrap();
        let cmd_output = Some("gcc\n\"11.0.0\"");
        let compile = Compile {
            exe: OsString::from(&gcc),
            cwd: cwd.clone(),
            args: Vec::new(),
            env_vars: env_vars.clone(),
        };

        let key1 = get_hash_key(&cmd_output, &compile);
        let key2 = get_hash_key(&cmd_output, &compile);
        thread::sleep(Duration::from_millis(50));
        f.touch(gcc.to_str().unwrap()).unwrap();
        let key3 = get_hash_key(&cmd_output, &compile);
        assert_eq!(key1, key2);
        assert_ne!(key2, key3);

        // check that compiler executable name is in hash
        let clang = f.mk_bin("clang").unwrap();
        filetime::set_file_mtime(&clang, get_mtime(&gcc)).expect("success");
        assert_eq!(get_mtime(&gcc), get_mtime(&clang));
        let cmd_output = Some("clang\n\"11.0.0\"");
        let key4 = get_hash_key(
            &cmd_output,
            &Compile {
                exe: OsString::from(&clang),
                cwd,
                args: Vec::new(),
                env_vars,
            },
        );
        assert_ne!(key1, key4);
    }

    #[test]
    fn test_compiler_check_content() {
        let f = TestFixture::new();
        let cwd = OsString::from(f.tempdir.path());
        let env_vars = vec![(
            OsString::from("SCCACHE_COMPILERCHECK"),
            OsString::from("content"),
        )];
        let gcc = f
            .mk_bin_contents("gcc", |mut f| {
                f.write_all("1".as_bytes())?;
                Ok(())
            })
            .unwrap();
        let cmd_output = Some("gcc\n\"11.0.0\"");
        let compile = Compile {
            exe: OsString::from(&gcc),
            cwd: cwd.clone(),
            args: Vec::new(),
            env_vars: env_vars.clone(),
        };
        let key1 = get_hash_key(&cmd_output, &compile);
        f.mk_bin_contents("gcc", |mut f| {
            f.write_all("1".as_bytes())?;
            Ok(())
        })
        .unwrap();
        let key2 = get_hash_key(&cmd_output, &compile);
        f.mk_bin_contents("gcc", |mut f| {
            f.write_all("2".as_bytes())?;
            Ok(())
        })
        .unwrap();
        let key3 = get_hash_key(&cmd_output, &compile);
        assert_eq!(key1, key2);
        assert_ne!(key2, key3);

        // check that compiler executable name is in hash
        let clang = f
            .mk_bin_contents("clang", |mut f| {
                f.write_all("2".as_bytes())?;
                Ok(())
            })
            .unwrap();
        let cmd_output = Some("clang\n\"11.0.0\"");
        let key4 = get_hash_key(
            &cmd_output,
            &Compile {
                exe: OsString::from(&clang),
                cwd,
                args: Vec::new(),
                env_vars,
            },
        );
        assert_ne!(key3, key4);
    }

    #[test]
    fn test_compiler_check_string() {
        let f = TestFixture::new();
        let cwd = OsString::from(f.tempdir.path());
        let gcc = f.mk_bin("gcc").unwrap();
        let cmd_output = Some("gcc\n\"11.0.0\"");

        let key1 = get_hash_key(
            &cmd_output,
            &Compile {
                exe: OsString::from(&gcc),
                cwd: cwd.clone(),
                args: Vec::new(),
                env_vars: vec![(
                    OsString::from("SCCACHE_COMPILERCHECK"),
                    OsString::from("string:123"),
                )],
            },
        );
        let key2 = get_hash_key(
            &cmd_output,
            &Compile {
                exe: OsString::from(&gcc),
                cwd,
                args: Vec::new(),
                env_vars: vec![(
                    OsString::from("SCCACHE_COMPILERCHECK"),
                    OsString::from("string:456"),
                )],
            },
        );
        assert_ne!(key1, key2);
    }

    #[test]
    fn test_compiler_check_version() {
        let f = TestFixture::new();
        let cwd = OsString::from(f.tempdir.path());
        let env_vars = vec![(
            OsString::from("SCCACHE_COMPILERCHECK"),
            OsString::from("version"),
        )];
        let test = |(output, executable): &(&str, &PathBuf)| {
            get_hash_key(
                &Some(output),
                &Compile {
                    exe: OsString::from(executable),
                    cwd: cwd.clone(),
                    args: Vec::new(),
                    env_vars: env_vars.clone(),
                },
            )
        };

        let clang = f.mk_bin("clang").unwrap();
        let clangpp = f.mk_bin("clang++").unwrap();
        let gcc = f.mk_bin("gcc").unwrap();
        let gpp = f.mk_bin("g++").unwrap();
        // Make executables the same mtime
        let gcc_mtime = get_mtime(&gcc);
        filetime::set_file_mtime(&clang, gcc_mtime).expect("success");
        filetime::set_file_mtime(&clangpp, gcc_mtime).expect("success");
        filetime::set_file_mtime(&gpp, gcc_mtime).expect("success");

        let compilers = [
            ("clang\n\"11.0.0\"", &clang),
            ("clang\n\"12.0.0\"", &clang),
            ("clang\n\"11.0.0\"", &clangpp),
            ("gcc\n\"11.0.0\"", &gcc),
            ("gcc\n\"11.1.0\"", &gcc),
            ("gcc\n\"11.0.0\"", &gpp),
        ];

        // Check that elements in `compilers` have different hashes.
        let mut results: Vec<String> = compilers.iter().map(test).collect();
        assert_eq!(results.len(), 6);
        results.sort();
        for c in results.windows(2) {
            assert_ne!(c[0], c[1]);
        }

        // Check that elements in `compilers` have different hashes due to
        // having different executable name.
        assert_ne!(results[0], results[2]);

        // If the compiler has unexpected output, bail out.

        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        next_command(&creator, Ok(MockChild::new(exit_status(0), "", "")));
        assert!(detect_compiler(
            creator.clone(),
            &Compile {
                exe: OsString::from(&gcc),
                cwd: cwd.clone(),
                args: Vec::new(),
                env_vars: env_vars.clone(),
            },
            pool,
            None
        )
        .wait()
        .is_err());

        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc\n", "")));
        assert!(detect_compiler(
            creator.clone(),
            &Compile {
                exe: OsString::from(&gcc),
                cwd: cwd.clone(),
                args: Vec::new(),
                env_vars: env_vars.clone(),
            },
            pool,
            None
        )
        .wait()
        .is_err());

        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "gcc\n__VERSION__", "")),
        );
        assert!(detect_compiler(
            creator,
            &Compile {
                exe: OsString::from(&gcc),
                cwd,
                args: Vec::new(),
                env_vars,
            },
            pool,
            None
        )
        .wait()
        .is_err());
    }

    #[test]
    fn test_get_compiler_info() {
        let creator = new_creator();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle();
        let f = TestFixture::new();
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator, &create_compile(&f), pool, None)
            .wait()
            .unwrap()
            .0;
        // digest of an empty file.
        assert_eq!(CompilerKind::C(CCompilerKind::Gcc), c.kind());
    }

    #[test]
    fn test_compiler_get_cached_or_compile() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = Runtime::new().unwrap();
        let pool = runtime.handle().clone();
        let storage = DiskCache::new(&f.tempdir.path().join("cache"), u64::MAX, &pool);
        let storage = Arc::new(storage);
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        // The preprocessor invocation.
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        // The compiler invocation.
        const COMPILER_STDOUT: &[u8] = b"compiler stdout";
        const COMPILER_STDERR: &[u8] = b"compiler stderr";
        let obj = f.tempdir.path().join("foo.o");
        let o = obj.clone();
        next_command_calls(&creator, move |_| {
            // Pretend to compile something.
            let mut f = File::create(&o)?;
            f.write_all(b"file contents")?;
            Ok(MockChild::new(
                exit_status(0),
                COMPILER_STDOUT,
                COMPILER_STDERR,
            ))
        });
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        let hasher2 = hasher.clone();
        let (cached, res) = runtime
            .block_on(async {
                hasher
                    .get_cached_or_compile(
                        None,
                        creator.clone(),
                        storage.clone(),
                        arguments.clone(),
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool.clone(),
                    )
                    .await
            })
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        match cached {
            CompileResult::CacheMiss(MissType::Normal, DistType::NoDist, _, f) => {
                // wait on cache write future so we don't race with it!
                f.wait().unwrap();
            }
            _ => panic!("Unexpected compile result: {:?}", cached),
        }
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
        // Now compile again, which should be a cache hit.
        fs::remove_file(&obj).unwrap();
        // The preprocessor invocation.
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        // There should be no actual compiler invocation.
        let (cached, res) = runtime
            .block_on(async {
                hasher2
                    .get_cached_or_compile(
                        None,
                        creator,
                        storage,
                        arguments,
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool,
                    )
                    .await
            })
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        assert_eq!(CompileResult::CacheHit(Duration::new(0, 0)), cached);
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_compiler_get_cached_or_compile_dist() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = Runtime::new().unwrap();
        let pool = runtime.handle().clone();
        let storage = DiskCache::new(&f.tempdir.path().join("cache"), u64::MAX, &pool);
        let storage = Arc::new(storage);
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        // The preprocessor invocation.
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        // The compiler invocation.
        const COMPILER_STDOUT: &[u8] = b"compiler stdout";
        const COMPILER_STDERR: &[u8] = b"compiler stderr";
        let obj = f.tempdir.path().join("foo.o");
        // Dist client will do the compilation
        let dist_client = Some(test_dist::OneshotClient::new(
            0,
            COMPILER_STDOUT.to_owned(),
            COMPILER_STDERR.to_owned(),
        ));
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        let hasher2 = hasher.clone();
        let (cached, res) = runtime
            .block_on(async {
                hasher
                    .get_cached_or_compile(
                        dist_client.clone(),
                        creator.clone(),
                        storage.clone(),
                        arguments.clone(),
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool.clone(),
                    )
                    .await
            })
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        match cached {
            CompileResult::CacheMiss(MissType::Normal, DistType::Ok(_), _, f) => {
                // wait on cache write future so we don't race with it!
                f.wait().unwrap();
            }
            _ => panic!("Unexpected compile result: {:?}", cached),
        }
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
        // Now compile again, which should be a cache hit.
        fs::remove_file(&obj).unwrap();
        // The preprocessor invocation.
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        // There should be no actual compiler invocation.
        let (cached, res) = runtime
            .block_on(async {
                hasher2
                    .get_cached_or_compile(
                        dist_client.clone(),
                        creator,
                        storage,
                        arguments,
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool,
                    )
                    .await
            })
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        assert_eq!(CompileResult::CacheHit(Duration::new(0, 0)), cached);
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
    }

    #[test]
    /// Test that a cache read that results in an error is treated as a cache
    /// miss.
    fn test_compiler_get_cached_or_compile_cache_error() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = Runtime::new().unwrap();
        let pool = runtime.handle().clone();
        let storage = MockStorage::new();
        let storage: Arc<MockStorage> = Arc::new(storage);
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        // The preprocessor invocation.
        next_command(
            &creator,
            Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
        );
        // The compiler invocation.
        const COMPILER_STDOUT: &[u8] = b"compiler stdout";
        const COMPILER_STDERR: &[u8] = b"compiler stderr";
        let obj = f.tempdir.path().join("foo.o");
        let o = obj.clone();
        next_command_calls(&creator, move |_| {
            // Pretend to compile something.
            let mut f = File::create(&o)?;
            f.write_all(b"file contents")?;
            Ok(MockChild::new(
                exit_status(0),
                COMPILER_STDOUT,
                COMPILER_STDERR,
            ))
        });
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        // The cache will return an error.
        storage.next_get(Err(anyhow!("Some Error")));
        let (cached, res) = runtime
            .block_on(hasher.get_cached_or_compile(
                None,
                creator,
                storage,
                arguments.clone(),
                cwd.to_path_buf(),
                vec![],
                CacheControl::Default,
                pool,
            ))
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        match cached {
            CompileResult::CacheMiss(MissType::CacheReadError, DistType::NoDist, _, f) => {
                // wait on cache write future so we don't race with it!
                let _ = f.wait();
            }
            _ => panic!("Unexpected compile result: {:?}", cached),
        }

        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
    }

    #[test]
    fn test_compiler_get_cached_or_compile_force_recache() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle().clone();
        let storage = DiskCache::new(&f.tempdir.path().join("cache"), u64::MAX, &pool);
        let storage = Arc::new(storage);
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        const COMPILER_STDOUT: &[u8] = b"compiler stdout";
        const COMPILER_STDERR: &[u8] = b"compiler stderr";
        // The compiler should be invoked twice, since we're forcing
        // recaching.
        let obj = f.tempdir.path().join("foo.o");
        for _ in 0..2 {
            // The preprocessor invocation.
            next_command(
                &creator,
                Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
            );
            // The compiler invocation.
            let o = obj.clone();
            next_command_calls(&creator, move |_| {
                // Pretend to compile something.
                let mut f = File::create(&o)?;
                f.write_all(b"file contents")?;
                Ok(MockChild::new(
                    exit_status(0),
                    COMPILER_STDOUT,
                    COMPILER_STDERR,
                ))
            });
        }
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        let hasher2 = hasher.clone();
        let (cached, res) = runtime
            .block_on(async {
                hasher
                    .get_cached_or_compile(
                        None,
                        creator.clone(),
                        storage.clone(),
                        arguments.clone(),
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool.clone(),
                    )
                    .await
            })
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        match cached {
            CompileResult::CacheMiss(MissType::Normal, DistType::NoDist, _, f) => {
                // wait on cache write future so we don't race with it!
                f.wait().unwrap();
            }
            _ => panic!("Unexpected compile result: {:?}", cached),
        }
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
        // Now compile again, but force recaching.
        fs::remove_file(&obj).unwrap();
        let (cached, res) = hasher2
            .get_cached_or_compile(
                None,
                creator,
                storage,
                arguments,
                cwd.to_path_buf(),
                vec![],
                CacheControl::ForceRecache,
                pool,
            )
            .wait()
            .unwrap();
        // Ensure that the object file was created.
        assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
        match cached {
            CompileResult::CacheMiss(MissType::ForcedRecache, DistType::NoDist, _, f) => {
                // wait on cache write future so we don't race with it!
                f.wait().unwrap();
            }
            _ => panic!("Unexpected compile result: {:?}", cached),
        }
        assert_eq!(exit_status(0), res.status);
        assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
        assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
    }

    #[test]
    fn test_compiler_get_cached_or_compile_preprocessor_error() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = single_threaded_runtime();
        let pool = runtime.handle().clone();
        let storage = DiskCache::new(&f.tempdir.path().join("cache"), u64::MAX, &pool);
        let storage = Arc::new(storage);
        // Pretend to be GCC.  Also inject a fake object file that the subsequent
        // preprocessor failure should remove.
        let obj = f.tempdir.path().join("foo.o");
        let o = obj.clone();
        next_command_calls(&creator, move |_| {
            let mut f = File::create(&o)?;
            f.write_all(b"file contents")?;
            Ok(MockChild::new(exit_status(0), "gcc", ""))
        });
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        // We should now have a fake object file.
        assert!(fs::metadata(&obj).is_ok());
        // The preprocessor invocation.
        const PREPROCESSOR_STDERR: &[u8] = b"something went wrong";
        next_command(
            &creator,
            Ok(MockChild::new(
                exit_status(1),
                b"preprocessor output",
                PREPROCESSOR_STDERR,
            )),
        );
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        let (cached, res) = runtime
            .block_on(async {
                hasher
                    .get_cached_or_compile(
                        None,
                        creator,
                        storage,
                        arguments,
                        cwd.to_path_buf(),
                        vec![],
                        CacheControl::Default,
                        pool,
                    )
                    .await
            })
            .unwrap();
        assert_eq!(cached, CompileResult::Error);
        assert_eq!(exit_status(1), res.status);
        // Shouldn't get anything on stdout, since that would just be preprocessor spew!
        assert_eq!(b"", res.stdout.as_slice());
        assert_eq!(PREPROCESSOR_STDERR, res.stderr.as_slice());
        // Errors in preprocessing should remove the object file.
        assert!(!fs::metadata(&obj).is_ok());
    }

    #[test]
    #[cfg(feature = "dist-client")]
    fn test_compiler_get_cached_or_compile_dist_error() {
        drop(env_logger::try_init());
        let creator = new_creator();
        let f = TestFixture::new();
        let runtime = Runtime::new().unwrap();
        let pool = runtime.handle().clone();
        let dist_clients = vec![
            test_dist::ErrorPutToolchainClient::new(),
            test_dist::ErrorAllocJobClient::new(),
            test_dist::ErrorSubmitToolchainClient::new(),
            test_dist::ErrorRunJobClient::new(),
        ];
        let storage = DiskCache::new(&f.tempdir.path().join("cache"), u64::MAX, &pool);
        let storage = Arc::new(storage);
        // Pretend to be GCC.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "gcc", "")));
        let c = get_compiler_info(creator.clone(), &create_compile(&f), &pool, None)
            .wait()
            .unwrap()
            .0;
        const COMPILER_STDOUT: &[u8] = b"compiler stdout";
        const COMPILER_STDERR: &[u8] = b"compiler stderr";
        // The compiler should be invoked twice, since we're forcing
        // recaching.
        let obj = f.tempdir.path().join("foo.o");
        for _ in dist_clients.iter() {
            // The preprocessor invocation.
            next_command(
                &creator,
                Ok(MockChild::new(exit_status(0), "preprocessor output", "")),
            );
            // The compiler invocation.
            let o = obj.clone();
            next_command_calls(&creator, move |_| {
                // Pretend to compile something.
                let mut f = File::create(&o)?;
                f.write_all(b"file contents")?;
                Ok(MockChild::new(
                    exit_status(0),
                    COMPILER_STDOUT,
                    COMPILER_STDERR,
                ))
            });
        }
        let cwd = f.tempdir.path();
        let arguments = ovec!["-c", "foo.c", "-o", "foo.o"];
        let hasher = match c.parse_arguments(
            &arguments,
            ".".as_ref(),
            None,
            #[cfg(feature = "dist-client")]
            false,
        ) {
            CompilerArguments::Ok(h) => h,
            o => panic!("Bad result from parse_arguments: {:?}", o),
        };
        // All these dist clients will fail, but should still result in successful compiles
        for dist_client in dist_clients {
            if obj.is_file() {
                fs::remove_file(&obj).unwrap();
            }
            let hasher = hasher.clone();
            let (cached, res) = hasher
                .get_cached_or_compile(
                    Some(dist_client.clone()),
                    creator.clone(),
                    storage.clone(),
                    arguments.clone(),
                    cwd.to_path_buf(),
                    vec![],
                    CacheControl::ForceRecache,
                    pool.clone(),
                )
                .wait()
                .expect("Does not error if storage put fails. qed");
            // Ensure that the object file was created.
            assert!(fs::metadata(&obj).map(|m| m.len() > 0).unwrap());
            match cached {
                CompileResult::CacheMiss(MissType::ForcedRecache, DistType::Error, _, f) => {
                    // wait on cache write future so we don't race with it!
                    f.wait().unwrap();
                }
                _ => panic!("Unexpected compile result: {:?}", cached),
            }
            assert_eq!(exit_status(0), res.status);
            assert_eq!(COMPILER_STDOUT, res.stdout.as_slice());
            assert_eq!(COMPILER_STDERR, res.stderr.as_slice());
        }
    }
}

#[cfg(test)]
#[cfg(feature = "dist-client")]
mod test_dist {
    use crate::dist::pkg;
    use crate::dist::{
        self, AllocJobResult, CompileCommand, JobAlloc, JobComplete, JobId, OutputData,
        PathTransformer, ProcessOutput, RunJobResult, SchedulerStatusResult, ServerId,
        SubmitToolchainResult, Toolchain,
    };
    use std::path::{Path, PathBuf};
    use std::sync::{atomic::AtomicBool, Arc};

    use crate::errors::*;

    pub struct ErrorPutToolchainClient;
    impl ErrorPutToolchainClient {
        #[allow(clippy::new_ret_no_self)]
        pub fn new() -> Arc<dyn dist::Client> {
            Arc::new(ErrorPutToolchainClient)
        }
    }
    #[async_trait]
    impl dist::Client for ErrorPutToolchainClient {
        async fn do_alloc_job(&self, _: Toolchain) -> Result<AllocJobResult> {
            unreachable!()
        }
        async fn do_get_status(&self) -> Result<SchedulerStatusResult> {
            unreachable!()
        }
        async fn do_submit_toolchain(
            &self,
            _: JobAlloc,
            _: Toolchain,
        ) -> Result<SubmitToolchainResult> {
            unreachable!()
        }
        async fn do_run_job(
            &self,
            _: JobAlloc,
            _: CompileCommand,
            _: Vec<String>,
            _: Box<dyn pkg::InputsPackager>,
        ) -> Result<(RunJobResult, PathTransformer)> {
            unreachable!()
        }
        async fn put_toolchain(
            &self,
            _: PathBuf,
            _: String,
            _: Box<dyn pkg::ToolchainPackager>,
        ) -> Result<(Toolchain, Option<(String, PathBuf)>)> {
            Err(anyhow!("MOCK: put toolchain failure"))
        }
        fn rewrite_includes_only(&self) -> bool {
            false
        }
        fn get_custom_toolchain(&self, _exe: &Path) -> Option<PathBuf> {
            None
        }
    }

    pub struct ErrorAllocJobClient {
        tc: Toolchain,
    }
    impl ErrorAllocJobClient {
        #[allow(clippy::new_ret_no_self)]
        pub fn new() -> Arc<dyn dist::Client> {
            Arc::new(Self {
                tc: Toolchain {
                    archive_id: "somearchiveid".to_owned(),
                },
            })
        }
    }
    #[async_trait]
    impl dist::Client for ErrorAllocJobClient {
        async fn do_alloc_job(&self, tc: Toolchain) -> Result<AllocJobResult> {
            assert_eq!(self.tc, tc);
            Err(anyhow!("MOCK: alloc job failure"))
        }
        async fn do_get_status(&self) -> Result<SchedulerStatusResult> {
            unreachable!()
        }
        async fn do_submit_toolchain(
            &self,
            _: JobAlloc,
            _: Toolchain,
        ) -> Result<SubmitToolchainResult> {
            unreachable!()
        }
        async fn do_run_job(
            &self,
            _: JobAlloc,
            _: CompileCommand,
            _: Vec<String>,
            _: Box<dyn pkg::InputsPackager>,
        ) -> Result<(RunJobResult, PathTransformer)> {
            unreachable!()
        }
        async fn put_toolchain(
            &self,
            _: PathBuf,
            _: String,
            _: Box<dyn pkg::ToolchainPackager>,
        ) -> Result<(Toolchain, Option<(String, PathBuf)>)> {
            Ok((self.tc.clone(), None))
        }
        fn rewrite_includes_only(&self) -> bool {
            false
        }
        fn get_custom_toolchain(&self, _exe: &Path) -> Option<PathBuf> {
            None
        }
    }

    pub struct ErrorSubmitToolchainClient {
        has_started: AtomicBool,
        tc: Toolchain,
    }
    impl ErrorSubmitToolchainClient {
        #[allow(clippy::new_ret_no_self)]
        pub fn new() -> Arc<dyn dist::Client> {
            Arc::new(Self {
                has_started: AtomicBool::default(),
                tc: Toolchain {
                    archive_id: "somearchiveid".to_owned(),
                },
            })
        }
    }

    #[async_trait]
    impl dist::Client for ErrorSubmitToolchainClient {
        async fn do_alloc_job(&self, tc: Toolchain) -> Result<AllocJobResult> {
            assert!(!self
                .has_started
                .swap(true, std::sync::atomic::Ordering::AcqRel));
            assert_eq!(self.tc, tc);
            Ok(AllocJobResult::Success {
                job_alloc: JobAlloc {
                    auth: "abcd".to_owned(),
                    job_id: JobId(0),
                    server_id: ServerId::new(([0, 0, 0, 0], 1).into()),
                },
                need_toolchain: true,
            })
        }
        async fn do_get_status(&self) -> Result<SchedulerStatusResult> {
            unreachable!("fn do_get_status is not used for this test. qed")
        }
        async fn do_submit_toolchain(
            &self,
            job_alloc: JobAlloc,
            tc: Toolchain,
        ) -> Result<SubmitToolchainResult> {
            assert_eq!(job_alloc.job_id, JobId(0));
            assert_eq!(self.tc, tc);
            Err(anyhow!("MOCK: submit toolchain failure"))
        }
        async fn do_run_job(
            &self,
            _: JobAlloc,
            _: CompileCommand,
            _: Vec<String>,
            _: Box<dyn pkg::InputsPackager>,
        ) -> Result<(RunJobResult, PathTransformer)> {
            unreachable!("fn do_run_job is not used for this test. qed")
        }
        async fn put_toolchain(
            &self,
            _: PathBuf,
            _: String,
            _: Box<dyn pkg::ToolchainPackager>,
        ) -> Result<(Toolchain, Option<(String, PathBuf)>)> {
            Ok((self.tc.clone(), None))
        }
        fn rewrite_includes_only(&self) -> bool {
            false
        }
        fn get_custom_toolchain(&self, _exe: &Path) -> Option<PathBuf> {
            None
        }
    }

    pub struct ErrorRunJobClient {
        has_started: AtomicBool,
        tc: Toolchain,
    }
    impl ErrorRunJobClient {
        #[allow(clippy::new_ret_no_self)]
        pub fn new() -> Arc<dyn dist::Client> {
            Arc::new(Self {
                has_started: AtomicBool::default(),
                tc: Toolchain {
                    archive_id: "somearchiveid".to_owned(),
                },
            })
        }
    }

    #[async_trait]
    impl dist::Client for ErrorRunJobClient {
        async fn do_alloc_job(&self, tc: Toolchain) -> Result<AllocJobResult> {
            assert!(!self
                .has_started
                .swap(true, std::sync::atomic::Ordering::AcqRel));
            assert_eq!(self.tc, tc);
            Ok(AllocJobResult::Success {
                job_alloc: JobAlloc {
                    auth: "abcd".to_owned(),
                    job_id: JobId(0),
                    server_id: ServerId::new(([0, 0, 0, 0], 1).into()),
                },
                need_toolchain: true,
            })
        }
        async fn do_get_status(&self) -> Result<SchedulerStatusResult> {
            unreachable!()
        }
        async fn do_submit_toolchain(
            &self,
            job_alloc: JobAlloc,
            tc: Toolchain,
        ) -> Result<SubmitToolchainResult> {
            assert_eq!(job_alloc.job_id, JobId(0));
            assert_eq!(self.tc, tc);
            Ok(SubmitToolchainResult::Success)
        }
        async fn do_run_job(
            &self,
            job_alloc: JobAlloc,
            command: CompileCommand,
            _: Vec<String>,
            _: Box<dyn pkg::InputsPackager>,
        ) -> Result<(RunJobResult, PathTransformer)> {
            assert_eq!(job_alloc.job_id, JobId(0));
            assert_eq!(command.executable, "/overridden/compiler");
            Err(anyhow!("MOCK: run job failure"))
        }
        async fn put_toolchain(
            &self,
            _: PathBuf,
            _: String,
            _: Box<dyn pkg::ToolchainPackager>,
        ) -> Result<(Toolchain, Option<(String, PathBuf)>)> {
            Ok((
                self.tc.clone(),
                Some((
                    "/overridden/compiler".to_owned(),
                    PathBuf::from("somearchiveid"),
                )),
            ))
        }
        fn rewrite_includes_only(&self) -> bool {
            false
        }
        fn get_custom_toolchain(&self, _exe: &Path) -> Option<PathBuf> {
            None
        }
    }

    pub struct OneshotClient {
        has_started: AtomicBool,
        tc: Toolchain,
        output: ProcessOutput,
    }

    impl OneshotClient {
        #[allow(clippy::new_ret_no_self)]
        pub fn new(code: i32, stdout: Vec<u8>, stderr: Vec<u8>) -> Arc<dyn dist::Client> {
            Arc::new(Self {
                has_started: AtomicBool::default(),
                tc: Toolchain {
                    archive_id: "somearchiveid".to_owned(),
                },
                output: ProcessOutput::fake_output(code, stdout, stderr),
            })
        }
    }

    #[async_trait]
    impl dist::Client for OneshotClient {
        async fn do_alloc_job(&self, tc: Toolchain) -> Result<AllocJobResult> {
            assert!(!self
                .has_started
                .swap(true, std::sync::atomic::Ordering::AcqRel));
            assert_eq!(self.tc, tc);

            Ok(AllocJobResult::Success {
                job_alloc: JobAlloc {
                    auth: "abcd".to_owned(),
                    job_id: JobId(0),
                    server_id: ServerId::new(([0, 0, 0, 0], 1).into()),
                },
                need_toolchain: true,
            })
        }
        async fn do_get_status(&self) -> Result<SchedulerStatusResult> {
            unreachable!("fn do_get_status is not used for this test. qed")
        }
        async fn do_submit_toolchain(
            &self,
            job_alloc: JobAlloc,
            tc: Toolchain,
        ) -> Result<SubmitToolchainResult> {
            assert_eq!(job_alloc.job_id, JobId(0));
            assert_eq!(self.tc, tc);

            Ok(SubmitToolchainResult::Success)
        }
        async fn do_run_job(
            &self,
            job_alloc: JobAlloc,
            command: CompileCommand,
            outputs: Vec<String>,
            inputs_packager: Box<dyn pkg::InputsPackager>,
        ) -> Result<(RunJobResult, PathTransformer)> {
            assert_eq!(job_alloc.job_id, JobId(0));
            assert_eq!(command.executable, "/overridden/compiler");

            let mut inputs = vec![];
            let path_transformer = inputs_packager.write_inputs(&mut inputs).unwrap();
            let outputs = outputs
                .into_iter()
                .map(|name| {
                    let data = format!("some data in {}", name);
                    let data = OutputData::try_from_reader(data.as_bytes()).unwrap();
                    (name, data)
                })
                .collect();
            let result = RunJobResult::Complete(JobComplete {
                output: self.output.clone(),
                outputs,
            });
            Ok((result, path_transformer))
        }
        async fn put_toolchain(
            &self,
            _: PathBuf,
            _: String,
            _: Box<dyn pkg::ToolchainPackager>,
        ) -> Result<(Toolchain, Option<(String, PathBuf)>)> {
            Ok((
                self.tc.clone(),
                Some((
                    "/overridden/compiler".to_owned(),
                    PathBuf::from("somearchiveid"),
                )),
            ))
        }
        fn rewrite_includes_only(&self) -> bool {
            false
        }
        fn get_custom_toolchain(&self, _exe: &Path) -> Option<PathBuf> {
            None
        }
    }
}
