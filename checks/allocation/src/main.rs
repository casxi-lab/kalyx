//! The allocation check of kalyx: every case of the answer vectors in
//! `vectors/r02.tsv`, run 100 times through the command entry under a
//! counting global allocator, leaves the live bytes at their baseline after
//! every run. The same program measures the resource profile of the
//! library, `docs/resource-profile.md`, when it is run with `profile`.
//!
//! The counting allocator forwards every allocation to the system allocator,
//! adds the size of each block that it hands out to the live bytes and
//! subtracts the size of each block that it takes back. The program embeds
//! the vector file when it is built, reads its 58 cases with the limits of
//! each and builds their requests first; the live bytes after that are the
//! baseline. Each run then creates a context with the limits of its case,
//! executes the request, writes the line of its outcome as a host does, with
//! the fallback step of the command contract for an error whose line does
//! not fit its own context, and drops all of them; the live bytes must be
//! back at the baseline, so a run leaves 0 bytes behind. Every run must end
//! with the result kind of its case and write a line, the same line as the
//! first run of its case, which the check compares by its length and a
//! checksum, so that it keeps no block across runs. Nothing is printed
//! before the last run, since the first print allocates the buffer of
//! standard output for the rest of the process. The program prints a
//! summary and exits with 0 when it ran every case `RUNS` times and every
//! run passes, and with 1 otherwise.
//!
//! Before it takes the baseline, the program tests its own measurement: a
//! job that keeps a block of 19 bytes must leave exactly 19 bytes behind,
//! and a job that frees all that it allocates must leave 0, so that a
//! measurement that always gives 0 fails the check instead of passing it.
//!
//! `profile` prints, for each case, the peak of the live bytes above the
//! baseline during one run, the blocks that the run allocates and the stack
//! that the run uses; and the same for deep inputs at several values of
//! `max_depth`. The stack is measured without any `unsafe` code. The
//! program runs the request again in a child process, `probe`, on a thread
//! with a stack of 1 MiB, below a number of padding frames that fill the
//! stack before the request runs, and searches for the most padding frames
//! under which the child still exits normally; a stack overflow ends the
//! child with a signal. The padding frames that the request displaces,
//! compared with a thread that runs nothing, times the bytes of one frame,
//! are the stack that it uses, to within one frame.
//!
//! This crate is not part of the kalyx package: the package forbids `unsafe`
//! code in every target, and a global allocator implements an unsafe trait.
//! The allocator wrapper is the only `unsafe` code here.

use std::alloc::{GlobalAlloc, Layout, System};
use std::io::Read;
use std::process::{Command, ExitCode, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use kalyx::command::serialize;
use kalyx::context::CancelFlag;
use kalyx::{Context, ErrorKind, FaultKind, Limits, Outcome, Request, Settled, execute};

/// The answer vectors, embedded when the program is built.
const VECTORS: &str = include_str!("../../../vectors/r02.tsv");

/// The header row of the vector file.
const HEADER: &str = "id\toperation\tvariable\tinput\tresult\tanswer\tlimits";

/// The cases of the vector file.
const CASES: usize = 58;

/// The runs of each case.
const RUNS: usize = 100;

/// The stack of the thread of a child process of the profile: 1 MiB, far
/// more than any probe needs.
const PROBE_STACK: usize = 1 << 20;

/// The most padding frames that the search of the profile tries: more than
/// fit on `PROBE_STACK`, since a frame holds at least 256 bytes.
const PADDING_CAP: u64 = 8_192;

/// The time that one child process of the search may take.
const PROBE_TIMEOUT: Duration = Duration::from_secs(60);

/// The runs that must all complete under the headroom of a probe.
const CONFIRMATIONS: usize = 10;

/// The values of `max_depth` of the deep inputs of the profile.
const DEPTHS: [u64; 4] = [128, 1_024, 8_192, 65_536];

/// The bytes of the blocks handed out and not yet taken back.
static LIVE: AtomicU64 = AtomicU64::new(0);

/// The largest value that `LIVE` reached since it was last reset.
static PEAK: AtomicU64 = AtomicU64::new(0);

/// The blocks handed out so far.
static BLOCKS: AtomicU64 = AtomicU64::new(0);

/// The system allocator, counting the bytes of the blocks it hands out and
/// takes back. The other methods of the trait keep their default bodies,
/// which call these two, so a reallocation counts as an allocation and a
/// deallocation.
struct Counting;

#[allow(
    unsafe_code,
    reason = "a global allocator implements the unsafe trait `GlobalAlloc`; this wrapper is the only unsafe code of the crate"
)]
// SAFETY: both methods pass their arguments unchanged to the system
// allocator and return what it returns, so every block and every layout
// meets the contract of `GlobalAlloc` as it does for `System`. The counts
// are atomics outside the blocks and never touch their memory.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller of `alloc` guarantees that `layout` has a
        // nonzero size, and the system allocator receives the same layout.
        let block = unsafe { System.alloc(layout) };
        if !block.is_null() {
            let size = layout.size() as u64;
            // The live bytes never come near `u64::MAX`; the addition cannot
            // panic inside the allocator in any case.
            let live = LIVE.fetch_add(size, Ordering::SeqCst).wrapping_add(size);
            PEAK.fetch_max(live, Ordering::SeqCst);
            BLOCKS.fetch_add(1, Ordering::SeqCst);
        }
        block
    }

    unsafe fn dealloc(&self, block: *mut u8, layout: Layout) {
        // SAFETY: the caller of `dealloc` guarantees that `block` was handed
        // out by this allocator with `layout`, and every such block came from
        // the system allocator with the same layout.
        unsafe { System.dealloc(block, layout) };
        LIVE.fetch_sub(layout.size() as u64, Ordering::SeqCst);
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

// ---------------------------------------------------------------------------
// The cases

/// One case of the vector file: its id, its request, the result kind that it
/// must end with and its limits.
struct Case<'a> {
    id: &'a str,
    request: Request,
    result: &'a str,
    limits: Limits,
}

/// Reads the cases of a vector file: the header row, then one case per
/// line with seven tab-separated columns. `tests/vectors.rs` in the package
/// checks the format itself; this reader only rejects what it cannot use.
fn cases(text: &str) -> Result<Vec<Case<'_>>, String> {
    let mut lines = text.lines();
    if lines.next() != Some(HEADER) {
        return Err("line 1: expected the header row".to_owned());
    }
    let mut cases = Vec::new();
    for (index, line) in lines.enumerate() {
        let at = index + 2;
        let columns: Vec<&str> = line.split('\t').collect();
        let [id, operation, variable, input, result, _answer, limits] = columns.as_slice() else {
            return Err(format!("line {at}: {} columns instead of 7", columns.len()));
        };
        let limits = case_limits(limits).map_err(|message| format!("line {at}: {message}"))?;
        cases.push(Case {
            id,
            request: Request::new(operation, variable, input),
            result,
            limits,
        });
    }
    Ok(cases)
}

/// The limits of the `limits` column: the defaults, with the `field=value`
/// settings of the column, separated by `;`, applied on top; `-` for none.
fn case_limits(column: &str) -> Result<Limits, String> {
    let mut limits = Limits::new();
    if column == "-" {
        return Ok(limits);
    }
    for setting in column.split(';') {
        let Some((field, value)) = setting.split_once('=') else {
            return Err(format!("limit setting without '=': {setting}"));
        };
        let Ok(value) = value.parse::<u64>() else {
            return Err(format!("limit value is not a u64: {setting}"));
        };
        limits = match field {
            "max_work" => limits.with_max_work(value),
            "max_input_bytes" => limits.with_max_input_bytes(value),
            "max_output_bytes" => limits.with_max_output_bytes(value),
            "max_depth" => limits.with_max_depth(value),
            "max_nodes" => limits.with_max_nodes(value),
            "max_storage_bytes" => limits.with_max_storage_bytes(value),
            "max_integer_bits" => limits.with_max_integer_bits(value),
            "max_exponent" => limits.with_max_exponent(value),
            "max_frames" => limits.with_max_frames(value),
            _ => return Err(format!("unknown Limits field: {field}")),
        };
    }
    Ok(limits)
}

/// The result kind of an outcome, as the `result` column of the vector file
/// names it: `ok` for a value, `state` for a state, and the kind of an
/// error.
fn result_kind(outcome: &Outcome) -> &'static str {
    match outcome.result() {
        Ok(Settled::Value(_)) => "ok",
        Ok(_) => "state",
        Err(error) => match error.kind() {
            ErrorKind::ResourceLimit => "ResourceLimit",
            ErrorKind::Cancelled => "Cancelled",
            ErrorKind::DeadlineExceeded => "DeadlineExceeded",
            ErrorKind::Fault(FaultKind::Syntax) => "Syntax",
            ErrorKind::Fault(FaultKind::UnknownSymbol) => "UnknownSymbol",
            ErrorKind::Fault(FaultKind::DivisionByZero) => "DivisionByZero",
            ErrorKind::Fault(FaultKind::NonIntegerExponent) => "NonIntegerExponent",
            ErrorKind::Fault(FaultKind::NotPolynomial) => "NotPolynomial",
            ErrorKind::Fault(FaultKind::Unsupported) => "Unsupported",
            ErrorKind::Fault(FaultKind::Internal) => "Internal",
            _ => "another kind",
        },
    }
}

/// The line that a host publishes for `outcome`, written under `own`, the
/// context of its request; when that fails and the outcome is an error, the
/// line written under a fresh context, by the fallback step of the command
/// contract. A value or a state is never written again.
fn publish(outcome: &Outcome, own: &mut Context) -> Option<Vec<u8>> {
    match serialize(outcome, own) {
        Ok(line) => Some(line),
        Err(_) => match outcome.result() {
            Err(_) => {
                let mut fresh = Context::new(Limits::new(), CancelFlag::new());
                serialize(outcome, &mut fresh).ok()
            }
            Ok(_) => None,
        },
    }
}

// ---------------------------------------------------------------------------
// The runs and their verdict

/// What one run left behind and wrote.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Run {
    /// The live bytes after the run, less the baseline.
    left: i128,
    /// The result kind of the outcome.
    result: &'static str,
    /// The length of the published line, or `None` when it has none.
    length: Option<usize>,
    /// The FNV-1a checksum of the line.
    checksum: u64,
    /// The largest number of live bytes above the baseline during the run.
    peak: u64,
}

/// The FNV-1a checksum of `bytes`, computed without allocating.
fn checksum(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// Measures `job` against `baseline`: `job` returns a result kind and the
/// line that it published, if any; the line is dropped before the live bytes
/// are read, so the run leaves behind only what `job` kept.
fn measure(baseline: u64, job: impl FnOnce() -> (&'static str, Option<Vec<u8>>)) -> Run {
    PEAK.store(LIVE.load(Ordering::SeqCst), Ordering::SeqCst);
    let (result, length, sum) = match job() {
        (result, Some(line)) => (result, Some(line.len()), checksum(&line)),
        (result, None) => (result, None, 0),
    };
    Run {
        left: i128::from(LIVE.load(Ordering::SeqCst)) - i128::from(baseline),
        result,
        length,
        checksum: sum,
        peak: PEAK.load(Ordering::SeqCst).saturating_sub(baseline),
    }
}

/// One run of `request` under `limits`, in a context of its own, measured
/// against `baseline`.
fn run(request: &Request, limits: Limits, baseline: u64) -> Run {
    measure(baseline, || {
        let mut context = Context::new(limits, CancelFlag::new());
        let outcome = execute(request, &mut context);
        (result_kind(&outcome), publish(&outcome, &mut context))
    })
}

/// The bytes of the block that the self-test keeps.
const KEPT: usize = 19;

/// The self-test of the measurement, run on one thread before the baseline:
/// a job that keeps a block of `KEPT` bytes leaves `KEPT` bytes behind, and
/// a job that frees the block that it allocates leaves 0; both reach a peak
/// of at least `KEPT` bytes. The kept block stays allocated for the rest of
/// the process, below the baseline.
fn self_test() -> bool {
    let kept = measure(LIVE.load(Ordering::SeqCst), || {
        std::mem::forget(Vec::<u8>::with_capacity(KEPT));
        ("ok", None)
    });
    let freed = measure(LIVE.load(Ordering::SeqCst), || {
        ("ok", Some(Vec::with_capacity(KEPT)))
    });
    let kept_bytes = i128::try_from(KEPT).unwrap_or(i128::MAX);
    let at_least = u64::try_from(KEPT).unwrap_or(u64::MAX);
    kept.left == kept_bytes && freed.left == 0 && kept.peak >= at_least && freed.peak >= at_least
}

/// The indices of the runs of one case that fail: a run fails when it left
/// bytes behind, ended with another result kind than `expected`, published
/// no line or wrote another line than the first run.
fn failures(runs: &[Run], expected: &str) -> Vec<usize> {
    let Some(first) = runs.first() else {
        return Vec::new();
    };
    let mut failed = Vec::new();
    for (index, found) in runs.iter().enumerate() {
        if found.left != 0
            || found.result != expected
            || found.length.is_none()
            || (found.length, found.checksum) != (first.length, first.checksum)
        {
            failed.push(index);
        }
    }
    failed
}

/// The exit status of the check: 0 when no run failed, 1 otherwise.
fn status(failures: usize) -> u8 {
    if failures == 0 { 0 } else { 1 }
}

/// The runs that the check recorded beyond or short of `RUNS` runs for each
/// of the `CASES` cases: 0 when it ran every case `RUNS` times.
fn shortfall(runs: usize) -> usize {
    (CASES * RUNS).abs_diff(runs)
}

/// The check: every case, `RUNS` times.
fn check() -> ExitCode {
    let cases = match cases(VECTORS) {
        Ok(cases) if cases.len() == CASES => cases,
        Ok(cases) => {
            eprintln!(
                "allocation: vectors/r02.tsv has {} cases instead of {CASES}",
                cases.len()
            );
            return ExitCode::from(1);
        }
        Err(message) => {
            eprintln!("allocation: vectors/r02.tsv: {message}");
            return ExitCode::from(1);
        }
    };
    if !self_test() {
        eprintln!("allocation: the leak self-test failed");
        return ExitCode::from(1);
    }
    // Every run is recorded in room allocated before the baseline, so that
    // recording it allocates nothing.
    let mut runs: Vec<Run> = Vec::with_capacity(cases.len() * RUNS);
    let baseline = LIVE.load(Ordering::SeqCst);
    let blocks = BLOCKS.load(Ordering::SeqCst);
    for case in &cases {
        for _ in 0..RUNS {
            runs.push(run(&case.request, case.limits, baseline));
        }
    }
    let allocated = BLOCKS.load(Ordering::SeqCst) - blocks;
    if shortfall(runs.len()) != 0 {
        eprintln!(
            "allocation: {} runs instead of {}",
            runs.len(),
            CASES * RUNS
        );
        return ExitCode::from(1);
    }

    let mut failed = 0;
    let mut peak = (0, "");
    for (case, found) in cases.iter().zip(runs.chunks(RUNS)) {
        for index in failures(found, case.result) {
            let run = found[index];
            eprintln!(
                "{} run {}: {} bytes left behind, result {} (expected {}), line length {:?}, checksum {:016x}",
                case.id,
                index + 1,
                run.left,
                run.result,
                case.result,
                run.length,
                run.checksum
            );
            failed += 1;
        }
        for run in found {
            if run.peak > peak.0 {
                peak = (run.peak, case.id);
            }
        }
    }
    let total = runs.len();
    println!(
        "allocation: {} cases of vectors/r02.tsv, {RUNS} runs each, {total} runs, {allocated} blocks",
        total / RUNS
    );
    println!(
        "allocation: the largest peak {} bytes above the baseline of {baseline} bytes, in {}",
        peak.0, peak.1
    );
    if failed == 0 {
        println!(
            "allocation: every run left 0 bytes behind, ended with the result of its case and wrote the same line as the first run of its case"
        );
    } else {
        eprintln!("allocation: {failed} of {total} runs failed");
    }
    ExitCode::from(status(failed))
}

// ---------------------------------------------------------------------------
// The resource profile

/// The deep inputs of the profile, each a nesting of some levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    /// `eval` of `((…(1)…))`.
    Parentheses,
    /// `eval` of `1+(1+(…(1)…))`.
    RightSums,
    /// `diff` in `x` of `x+(x+(…(x)…))`.
    RightSumsOfX,
}

impl Shape {
    const ALL: [Self; 3] = [Self::Parentheses, Self::RightSums, Self::RightSumsOfX];

    fn name(self) -> &'static str {
        match self {
            Self::Parentheses => "parentheses",
            Self::RightSums => "right-sums",
            Self::RightSumsOfX => "right-sums-of-x",
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|shape| shape.name() == name)
    }

    /// The request of `levels` levels of this shape.
    fn request(self, levels: u64) -> Request {
        let levels = usize::try_from(levels).unwrap_or(usize::MAX);
        let (operation, open, leaf) = match self {
            Self::Parentheses => ("eval", "(", "1"),
            Self::RightSums => ("eval", "1+(", "1"),
            Self::RightSumsOfX => ("diff", "x+(", "x"),
        };
        let mut input = open.repeat(levels);
        input.push_str(leaf);
        input.push_str(&")".repeat(levels));
        Request::new(operation, "x", &input)
    }

    /// The levels of the deepest input of this shape that `max_depth`
    /// accepts.
    fn levels(self, max_depth: u64) -> u64 {
        match self {
            Self::Parentheses => max_depth.saturating_sub(1),
            Self::RightSums | Self::RightSumsOfX => max_depth.saturating_sub(1) / 2,
        }
    }
}

/// Limits wide enough for the deep inputs: `max_depth` as given, and every
/// other field far beyond what the inputs of the profile need.
fn deep_limits(max_depth: u64) -> Limits {
    Limits::new()
        .with_max_depth(max_depth)
        .with_max_work(1 << 40)
        .with_max_input_bytes(1 << 30)
        .with_max_output_bytes(1 << 30)
        .with_max_nodes(1 << 30)
        .with_max_storage_bytes(1 << 40)
}

/// What a child process runs: one case of the vectors, a deep input of some
/// levels under a `max_depth`, or nothing at all, which measures the stack
/// that a thread needs by itself.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Probe {
    Case(usize),
    Deep(Shape, u64, u64),
    Empty,
}

impl Probe {
    /// The arguments of the child process after `probe` and the number of
    /// padding frames.
    fn arguments(&self) -> Vec<String> {
        match self {
            Self::Case(index) => vec!["case".to_owned(), index.to_string()],
            Self::Deep(shape, levels, max_depth) => vec![
                "deep".to_owned(),
                shape.name().to_owned(),
                levels.to_string(),
                max_depth.to_string(),
            ],
            Self::Empty => vec!["empty".to_owned()],
        }
    }

    fn parse(arguments: &[String]) -> Result<Self, String> {
        let number = |text: &str| {
            text.parse::<u64>()
                .map_err(|_| format!("not a number: {text}"))
        };
        match arguments {
            [kind, index] if kind == "case" => {
                let index = number(index)?;
                usize::try_from(index)
                    .map(Self::Case)
                    .map_err(|_| format!("not an index: {index}"))
            }
            [kind, shape, levels, max_depth] if kind == "deep" => {
                let Some(shape) = Shape::from_name(shape) else {
                    return Err(format!("unknown shape: {shape}"));
                };
                Ok(Self::Deep(shape, number(levels)?, number(max_depth)?))
            }
            [kind] if kind == "empty" => Ok(Self::Empty),
            _ => Err(format!("unknown probe: {arguments:?}")),
        }
    }
}

/// The bytes of the buffer of one padding frame.
const PADDING_BYTES: usize = 256;

/// The addresses of the buffers of the first and the last padding frame,
/// 0 before they are filled.
#[derive(Clone, Copy, Debug, Default)]
struct Ends {
    first: usize,
    last: usize,
}

impl Ends {
    /// The mean stack that one of `frames` padding frames below the first
    /// takes: the distance between the first and the last buffer divided by
    /// `frames`, rounded down; 0 for no frames.
    fn stride(self, frames: u64) -> u64 {
        let span = u64::try_from(self.first.abs_diff(self.last)).unwrap_or(u64::MAX);
        span.checked_div(frames).unwrap_or(0)
    }
}

/// Fills `frames + 1` frames of the stack, each holding a buffer of
/// `PADDING_BYTES` bytes, then runs `job` below them and returns what it
/// returns; `ends` receives the addresses of the first and the last buffer.
#[inline(never)]
fn pad<T>(frames: u64, ends: &mut Ends, job: &mut dyn FnMut() -> T) -> T {
    let buffer = std::hint::black_box([0u8; PADDING_BYTES]);
    let here = std::ptr::from_ref(&buffer).addr();
    if ends.first == 0 {
        ends.first = here;
    }
    ends.last = here;
    let result = if frames == 0 {
        job()
    } else {
        pad(frames - 1, ends, job)
    };
    std::hint::black_box(&buffer);
    result
}

/// The child process: on a thread with a stack of `PROBE_STACK` bytes,
/// fills `frames` padding frames and runs `probe` below them, then prints
/// the result kind, the heap peak and the line length of the run and the
/// mean stride of a padding frame. When the padding and the run do not fit the
/// stack, the stack overflows and the process ends with a signal.
fn child(frames: u64, probe: &Probe) -> ExitCode {
    let job = match probe {
        Probe::Case(index) => match cases(VECTORS) {
            Ok(mut cases) if *index < cases.len() => {
                let case = cases.swap_remove(*index);
                Some((case.request, case.limits))
            }
            Ok(_) => {
                eprintln!("allocation: no case {index}");
                return ExitCode::from(2);
            }
            Err(message) => {
                eprintln!("allocation: vectors/r02.tsv: {message}");
                return ExitCode::from(2);
            }
        },
        Probe::Deep(shape, levels, max_depth) => {
            Some((shape.request(*levels), deep_limits(*max_depth)))
        }
        Probe::Empty => None,
    };
    let thread = std::thread::Builder::new()
        .stack_size(PROBE_STACK)
        .spawn(move || {
            let mut ends = Ends::default();
            let mut work = || match &job {
                Some((request, limits)) => {
                    let baseline = LIVE.load(Ordering::SeqCst);
                    let found = run(request, *limits, baseline);
                    (found.result, found.peak, found.length)
                }
                None => ("none", 0, None),
            };
            let found = pad(frames, &mut ends, &mut work);
            (found, ends.stride(frames))
        });
    let Ok(thread) = thread else {
        eprintln!("allocation: the thread could not be created");
        return ExitCode::from(2);
    };
    match thread.join() {
        Ok(((result, peak, length), stride)) => {
            let length = length.map_or_else(|| "-".to_owned(), |length| length.to_string());
            println!("{result} {peak} {length} {stride}");
            ExitCode::SUCCESS
        }
        Err(_) => ExitCode::from(2),
    }
}

/// What a child process reported: the result kind, the heap peak, the
/// length of the line, `-` for none, and the stride of a padding frame.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Report {
    result: String,
    peak: u64,
    line: String,
    stride: u64,
}

/// Runs `probe` in a child process below `frames` padding frames: the
/// report of the child when it exits normally, `None` when it ends with a
/// signal or another status, as a stack overflow does, and an error when it
/// cannot run or takes longer than `PROBE_TIMEOUT`.
fn fits(frames: u64, probe: &Probe) -> Result<Option<Report>, String> {
    let program = std::env::current_exe().map_err(|error| error.to_string())?;
    let mut child = Command::new(program)
        .arg("probe")
        .arg(frames.to_string())
        .args(probe.arguments())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| error.to_string())?;
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|error| error.to_string())? {
            break status;
        }
        if started.elapsed() > PROBE_TIMEOUT {
            // The child is killed and collected; a failure of either leaves
            // nothing that the profile could use.
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("{probe:?} below {frames} frames timed out"));
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    if !status.success() {
        return Ok(None);
    }
    let mut output = String::new();
    if let Some(mut stdout) = child.stdout.take() {
        stdout
            .read_to_string(&mut output)
            .map_err(|error| error.to_string())?;
    }
    report(&output).map(Some)
}

/// Reads the report line of a child process.
fn report(output: &str) -> Result<Report, String> {
    let fields: Vec<&str> = output.split_whitespace().collect();
    let [result, peak, line, stride] = fields.as_slice() else {
        return Err(format!("malformed report: {output:?}"));
    };
    let (Ok(peak), Ok(stride)) = (peak.parse(), stride.parse()) else {
        return Err(format!("malformed report: {output:?}"));
    };
    Ok(Report {
        result: (*result).to_owned(),
        peak,
        line: (*line).to_owned(),
        stride,
    })
}

/// The largest `k` from 0 to `cap` for which `fits` gives a value, found by
/// bisection on the assumption that `fits` gives a value for every number
/// below one for which it gives one; `None` when it gives none for 0.
/// Returns `k` with the value that `fits` gave for it.
fn largest<T>(
    cap: u64,
    mut fits: impl FnMut(u64) -> Result<Option<T>, String>,
) -> Result<Option<(u64, T)>, String> {
    let Some(mut found) = fits(0)? else {
        return Ok(None);
    };
    if let Some(at_cap) = fits(cap)? {
        return Ok(Some((cap, at_cap)));
    }
    let (mut low, mut high) = (0, cap);
    while high - low > 1 {
        let middle = low + (high - low) / 2;
        match fits(middle)? {
            Some(at_middle) => {
                low = middle;
                found = at_middle;
            }
            None => high = middle,
        }
    }
    Ok(Some((low, found)))
}

/// The most padding frames under which `probe` completes in each of
/// `CONFIRMATIONS` runs, with the report of the search. The search by
/// bisection gives a number of frames under which one run completed; the
/// number is lowered until every one of `CONFIRMATIONS` runs completes,
/// since the stack that one run uses can exceed that of another by a frame
/// or two, as the system allocator takes a longer path now and then.
fn headroom(probe: &Probe) -> Result<(u64, Report), String> {
    let (mut frames, report) = match largest(PADDING_CAP, |frames| fits(frames, probe))? {
        Some((frames, _)) if frames == PADDING_CAP => {
            return Err(format!(
                "{probe:?} completes below {PADDING_CAP} frames, so the stack never overflowed"
            ));
        }
        Some(found) => found,
        None => {
            return Err(format!(
                "{probe:?} does not complete on {PROBE_STACK} bytes"
            ));
        }
    };
    let mut confirmed = 0;
    while confirmed < CONFIRMATIONS {
        if fits(frames, probe)?.is_some() {
            confirmed += 1;
        } else if frames == 0 {
            return Err(format!("{probe:?} does not complete reliably"));
        } else {
            frames -= 1;
            confirmed = 0;
        }
    }
    Ok((frames, report))
}

/// The stack that `probe` uses beyond a thread that runs nothing, in bytes:
/// the padding frames that it displaces, times the stride of a frame.
fn stack_use(probe: &Probe, empty: u64, stride: u64) -> Result<(u64, Report), String> {
    let (frames, report) = headroom(probe)?;
    Ok((empty.saturating_sub(frames).saturating_mul(stride), report))
}

/// The profile: the heap peak, the blocks and the stack of every case, then
/// the heap peak and the stack of the deep inputs at each value of
/// `DEPTHS`, printed as the Markdown tables of the resource profile.
fn profile() -> Result<(), String> {
    let cases = cases(VECTORS)?;
    let (empty, report) = headroom(&Probe::Empty)?;
    let stride = report.stride;
    if stride == 0 {
        return Err("the stride of a padding frame was not measured".to_owned());
    }
    println!(
        "A thread of {PROBE_STACK} bytes that runs nothing holds {empty} padding frames of {stride} bytes."
    );
    println!();
    println!("| Case | Result | Heap peak (bytes) | Blocks | Stack (bytes) |");
    println!("| --- | --- | ---: | ---: | ---: |");
    for (index, case) in cases.iter().enumerate() {
        let baseline = LIVE.load(Ordering::SeqCst);
        let blocks = BLOCKS.load(Ordering::SeqCst);
        let found = run(&case.request, case.limits, baseline);
        let blocks = BLOCKS.load(Ordering::SeqCst) - blocks;
        let (stack, child) = stack_use(&Probe::Case(index), empty, stride)?;
        if child.result != case.result || found.result != case.result {
            return Err(format!(
                "{}: ended with {} and {}, expected {}",
                case.id, found.result, child.result, case.result
            ));
        }
        println!(
            "| `{}` | {} | {} | {blocks} | {stack} |",
            case.id, case.result, found.peak
        );
    }
    println!();
    println!("| Input | `max_depth` | Levels | Result | Heap peak (bytes) | Stack (bytes) |");
    println!("| --- | ---: | ---: | --- | ---: | ---: |");
    for shape in Shape::ALL {
        for max_depth in DEPTHS {
            let levels = shape.levels(max_depth);
            let (stack, child) = stack_use(&Probe::Deep(shape, levels, max_depth), empty, stride)?;
            println!(
                "| {} | {max_depth} | {levels} | {} | {} | {stack} |",
                shape.name(),
                child.result,
                child.peak
            );
        }
    }
    Ok(())
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.as_slice() {
        [] => check(),
        [mode] if mode == "profile" => match profile() {
            Ok(()) => ExitCode::SUCCESS,
            Err(message) => {
                eprintln!("allocation: profile: {message}");
                ExitCode::from(1)
            }
        },
        [mode, frames, rest @ ..] if mode == "probe" => {
            match (frames.parse::<u64>(), Probe::parse(rest)) {
                (Ok(frames), Ok(probe)) => child(frames, &probe),
                (_, Err(message)) => {
                    eprintln!("allocation: {message}");
                    ExitCode::from(2)
                }
                (Err(_), _) => {
                    eprintln!("allocation: not a number of frames: {frames}");
                    ExitCode::from(2)
                }
            }
        }
        _ => {
            eprintln!("usage: kalyx-allocation-check [profile]");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CASES, Ends, PADDING_BYTES, Probe, RUNS, Run, Shape, VECTORS, case_limits, cases, checksum,
        deep_limits, failures, largest, pad, report, run, shortfall, status,
    };
    use kalyx::{Limits, Request};

    // The check runs every case 100 times, and exits with 1 when a run
    // fails, so that the step that runs it fails.
    #[test]
    fn the_check_runs_100_times_and_fails_on_a_failed_run() {
        assert_eq!(RUNS, 100);
        assert_eq!(status(0), 0);
        assert_eq!(status(1), 1);
        assert_eq!(status(RUNS), 1);
    }

    // The check fails unless it ran every one of the 58 cases 100 times:
    // the runs of 57 cases, one run short or one run over are a shortfall.
    #[test]
    fn the_check_fails_unless_every_case_ran_100_times() {
        assert_eq!(CASES, 58);
        assert_eq!(shortfall(5_800), 0);
        assert_eq!(shortfall(57 * 100), 100);
        assert_eq!(shortfall(5_799), 1);
        assert_eq!(shortfall(5_801), 1);
        assert_eq!(shortfall(0), 5_800);
    }

    // The embedded vector file has its 58 cases, each with the limits of
    // its column: the four `ResourceLimit` cases set the field that they
    // exceed, two of them to its default, and the others keep the defaults.
    #[test]
    fn the_check_reads_the_58_cases_with_their_limits() {
        let cases = cases(VECTORS).unwrap();
        assert_eq!(cases.len(), CASES);
        let limited: Vec<(&str, &str, Limits)> = cases
            .iter()
            .filter(|case| case.result == "ResourceLimit" || case.limits != Limits::new())
            .map(|case| (case.id, case.result, case.limits))
            .collect();
        assert_eq!(
            limited,
            [
                (
                    "degree_limit_1",
                    "ResourceLimit",
                    Limits::new().with_max_exponent(256)
                ),
                (
                    "bit_limit_1",
                    "ResourceLimit",
                    Limits::new().with_max_integer_bits(4096)
                ),
                (
                    "depth_limit_1",
                    "ResourceLimit",
                    Limits::new().with_max_depth(128)
                ),
                (
                    "right_depth_limit_1",
                    "ResourceLimit",
                    Limits::new().with_max_depth(32)
                ),
            ]
        );
        assert_eq!(
            case_limits("max_work=7;max_frames=2").unwrap(),
            Limits::new().with_max_work(7).with_max_frames(2)
        );
    }

    // A file without its header row, a line without seven columns and an
    // unknown limit field are rejected.
    #[test]
    fn the_reader_rejects_what_it_cannot_use() {
        assert!(cases("a\teval\tx\t1\tok\t1\t-\n").is_err());
        let header = "id\toperation\tvariable\tinput\tresult\tanswer\tlimits\n";
        assert!(cases(&format!("{header}a\teval\tx\t1\tok\t1\n")).is_err());
        assert!(cases(&format!("{header}a\teval\tx\t1\tok\t1\tmax_degree=3\n")).is_err());
        assert!(case_limits("max_work").is_err());
        assert!(case_limits("max_work=-1").is_err());
    }

    // A run publishes the line of a value under its own context, and the
    // line of an error that does not fit its own context by the fallback
    // step: `eval` of `0*(1/0)` under `max_work = 24` has no line under its
    // own context and still publishes one.
    #[test]
    fn a_run_publishes_the_fallback_line_of_an_error() {
        let found = run(&Request::new("eval", "x", "1"), Limits::new(), 0);
        assert_eq!((found.result, found.length), ("ok", Some(14)));
        let request = Request::new("eval", "x", "0*(1/0)");
        let found = run(&request, Limits::new().with_max_work(24), 0);
        assert_eq!(found.result, "DivisionByZero");
        assert!(found.length.is_some());
    }

    /// A run that passes: nothing left behind, a value and a line.
    fn passing() -> Run {
        Run {
            left: 0,
            result: "ok",
            length: Some(12),
            checksum: checksum(b"value\t1\t2\t3\n"),
            peak: 100,
        }
    }

    // Runs that each leave nothing behind, end with the result of their case
    // and write the same line pass, whatever their peaks.
    #[test]
    fn equal_runs_without_leftovers_pass() {
        assert!(failures(&[passing(); 100], "ok").is_empty());
        assert!(failures(&[], "ok").is_empty());
        let mut runs = [passing(); 3];
        runs[1].peak = 7;
        assert!(failures(&runs, "ok").is_empty());
    }

    // A run that leaves bytes behind fails, also when every run leaves the
    // same amount, as a block that the first run keeps would; so does a run
    // that takes back more than it handed out.
    #[test]
    fn a_run_that_leaves_bytes_behind_fails() {
        let mut runs = [passing(); 4];
        runs[2].left = 19;
        assert_eq!(failures(&runs, "ok"), [2]);
        let leaking = Run {
            left: 19,
            ..passing()
        };
        assert_eq!(failures(&[leaking; 3], "ok"), [0, 1, 2]);
        runs[2].left = -8;
        assert_eq!(failures(&runs, "ok"), [2]);
    }

    // A run with another result kind than its case fails, and so does a run
    // without a line.
    #[test]
    fn a_run_with_another_result_or_without_a_line_fails() {
        let mut runs = [passing(); 3];
        runs[1].result = "ResourceLimit";
        assert_eq!(failures(&runs, "ok"), [1]);
        assert_eq!(failures(&[passing(); 2], "DivisionByZero"), [0, 1]);
        let mut runs = [passing(); 3];
        runs[2].length = None;
        assert_eq!(failures(&runs, "ok"), [2]);
        let unwritten = Run {
            length: None,
            ..passing()
        };
        assert_eq!(failures(&[unwritten; 2], "ok"), [0, 1]);
    }

    // A run whose line differs from the line of the first run fails, by its
    // length or by its checksum.
    #[test]
    fn a_run_with_another_line_fails() {
        let mut runs = [passing(); 3];
        runs[1].length = Some(13);
        runs[2].checksum = checksum(b"value\t1\t2\t4\n");
        assert_eq!(failures(&runs, "ok"), [1, 2]);
    }

    // The search finds the largest number for which the closure gives a
    // value, at 0, inside and at the cap, gives up when 0 gives none and
    // passes an error on.
    #[test]
    fn the_search_finds_the_largest_fitting_number() {
        for threshold in [0, 1, 100, 4_095, 8_191, 8_192] {
            let mut tried = 0;
            let found = largest(8_192, |frames| {
                tried += 1;
                Ok((frames <= threshold).then_some(frames))
            })
            .unwrap();
            assert_eq!(found, Some((threshold, threshold)), "{threshold}");
            assert!(tried <= 16, "{tried}");
        }
        let never = largest(8_192, |_| Ok(None::<()>)).unwrap();
        assert!(never.is_none());
        let error = largest(8_192, |_| Err::<Option<()>, _>("x".into()));
        assert!(error.is_err());
    }

    // Padding runs the job below its frames and measures the mean stride
    // of a frame, which holds at least the buffer of the frame.
    #[test]
    fn padding_runs_the_job_and_measures_the_stride_of_a_frame() {
        let mut ends = Ends::default();
        let mut calls = 0;
        let found = pad(50, &mut ends, &mut || {
            calls += 1;
            7
        });
        assert_eq!((found, calls), (7, 1));
        let stride = ends.stride(50);
        assert!(stride >= PADDING_BYTES as u64, "{stride}");
        assert!(stride < 4 * PADDING_BYTES as u64, "{stride}");
        assert_eq!(Ends::default().stride(0), 0);
    }

    // The arguments of a probe read back as the same probe, and the report
    // of a child reads back as its fields.
    #[test]
    fn probes_and_reports_read_back() {
        for probe in [
            Probe::Case(57),
            Probe::Deep(Shape::RightSumsOfX, 32_767, 65_536),
            Probe::Empty,
        ] {
            assert_eq!(Probe::parse(&probe.arguments()).unwrap(), probe);
        }
        let zigzag = ["deep", "zigzag", "1", "2"].map(String::from);
        assert!(Probe::parse(&zigzag).is_err());
        let found = report("ok 1234 17 288\n").unwrap();
        assert_eq!(
            (found.result.as_str(), found.peak, found.line.as_str()),
            ("ok", 1234, "17")
        );
        assert_eq!(found.stride, 288);
        assert!(report("ok\n").is_err());
    }

    // The deep inputs have the levels that their `max_depth` accepts, and
    // one level more is rejected by depth.
    #[test]
    fn the_deep_inputs_reach_their_depth_limit() {
        for shape in Shape::ALL {
            for max_depth in [16, 128] {
                let levels = shape.levels(max_depth);
                let accepted = run(&shape.request(levels), deep_limits(max_depth), 0);
                assert_eq!(accepted.result, "ok", "{shape:?} {max_depth}");
                let deeper = run(&shape.request(levels + 1), deep_limits(max_depth), 0);
                assert_eq!(deeper.result, "ResourceLimit", "{shape:?} {max_depth}");
            }
        }
    }
}
