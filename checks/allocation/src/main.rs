//! The allocation check of kalyx: one request, run 100 times through the
//! command entry under a counting global allocator, leaves the live bytes at
//! their baseline after every run.
//!
//! The counting allocator forwards every allocation to the system allocator,
//! adds the size of each block that it hands out to the live bytes and
//! subtracts the size of each block that it takes back. The request is built
//! first, and the live bytes after that are the baseline. Each run then
//! creates a context, executes the request, writes the line of its outcome
//! and drops all of them; the live bytes must be back at the baseline, so a
//! run leaves 0 bytes behind. Every run must also give the same line, which
//! the check compares by its length and a checksum, so that it keeps no
//! block across runs. Nothing is printed before the last run, since the
//! first print allocates the buffer of standard output for the rest of the
//! process. The program prints a summary and exits with 0 when every run
//! passes, and with 1 otherwise.
//!
//! This crate is not part of the kalyx package: the package forbids `unsafe`
//! code in every target, and a global allocator implements an unsafe trait.
//! The allocator wrapper is the only `unsafe` code here.

use std::alloc::{GlobalAlloc, Layout, System};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU64, Ordering};

use kalyx::command::serialize;
use kalyx::context::CancelFlag;
use kalyx::{Context, Limits, Request, Settled, execute};

/// The runs of the request.
const RUNS: usize = 100;

/// The bytes of the blocks handed out and not yet taken back.
static LIVE: AtomicU64 = AtomicU64::new(0);

/// The largest value that `LIVE` reached.
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

/// What one run left behind and wrote.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Run {
    /// The live bytes after the run, less the baseline.
    left: i128,
    /// Whether the request gave a value.
    value: bool,
    /// The length of the line, or `None` when it was not written.
    length: Option<usize>,
    /// The FNV-1a checksum of the line.
    checksum: u64,
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

/// One run of `request` in a context of its own, measured against
/// `baseline`.
fn run(request: &Request, baseline: u64) -> Run {
    let (value, length, sum) = {
        let mut context = Context::new(Limits::new(), CancelFlag::new());
        let outcome = execute(request, &mut context);
        let value = matches!(outcome.result(), Ok(Settled::Value(_)));
        match serialize(&outcome, &mut context) {
            Ok(line) => (value, Some(line.len()), checksum(&line)),
            Err(_) => (value, None, 0),
        }
    };
    Run {
        left: i128::from(LIVE.load(Ordering::SeqCst)) - i128::from(baseline),
        value,
        length,
        checksum: sum,
    }
}

/// The indices of the runs that fail: a run fails when it left bytes behind,
/// gave no value, wrote no line or differs from the first run.
fn failures(runs: &[Run]) -> Vec<usize> {
    let Some(first) = runs.first() else {
        return Vec::new();
    };
    let mut failed = Vec::new();
    for (index, found) in runs.iter().enumerate() {
        if found.left != 0 || !found.value || found.length.is_none() || found != first {
            failed.push(index);
        }
    }
    failed
}

fn main() -> ExitCode {
    let request = Request::new("diff", "x", "(x/2 + 1/3)^8 - x^3")
        .with_input_version(1)
        .with_context_version(2)
        .with_settings_version(3);
    let baseline = LIVE.load(Ordering::SeqCst);
    let blocks = BLOCKS.load(Ordering::SeqCst);
    let mut runs = [Run {
        left: 0,
        value: false,
        length: None,
        checksum: 0,
    }; RUNS];
    for slot in &mut runs {
        *slot = run(&request, baseline);
    }
    let allocated = BLOCKS.load(Ordering::SeqCst) - blocks;
    let peak = PEAK.load(Ordering::SeqCst).saturating_sub(baseline);

    let failed = failures(&runs);
    for index in &failed {
        let found = runs[*index];
        eprintln!(
            "run {}: {} bytes left behind, value {}, line length {:?}, checksum {:016x}",
            index + 1,
            found.left,
            found.value,
            found.length,
            found.checksum
        );
    }
    let failures = failed.len();
    let mut context = Context::new(Limits::new(), CancelFlag::new());
    let outcome = execute(&request, &mut context);
    let line = serialize(&outcome, &mut context)
        .map(|line| String::from_utf8_lossy(&line).into_owned())
        .unwrap_or_default();
    println!("allocation: the line {line:?}");
    println!(
        "allocation: {RUNS} runs, {allocated} blocks, a peak of {peak} bytes above the baseline of {baseline} bytes"
    );
    if failures == 0 {
        println!("allocation: every run left 0 bytes behind and wrote the same line");
    } else {
        eprintln!("allocation: {failures} of {RUNS} runs failed");
    }
    ExitCode::from(status(failures))
}

/// The exit status of the check: 0 when no run failed, 1 otherwise.
fn status(failures: usize) -> u8 {
    if failures == 0 { 0 } else { 1 }
}

#[cfg(test)]
mod tests {
    use super::{RUNS, Run, checksum, failures, status};

    // The check runs the request 100 times, and exits with 1 when a run
    // fails, so that the step that runs it fails.
    #[test]
    fn the_check_runs_100_times_and_fails_on_a_failed_run() {
        assert_eq!(RUNS, 100);
        assert_eq!(status(0), 0);
        assert_eq!(status(1), 1);
        assert_eq!(status(RUNS), 1);
    }

    /// A run that passes: nothing left behind, a value and a line.
    fn passing() -> Run {
        Run {
            left: 0,
            value: true,
            length: Some(12),
            checksum: checksum(b"value\t1\t2\t3\n"),
        }
    }

    // Runs that each leave nothing behind, give a value and write the same
    // line pass.
    #[test]
    fn equal_runs_without_leftovers_pass() {
        assert!(failures(&[passing(); 100]).is_empty());
        assert!(failures(&[]).is_empty());
    }

    // A run that leaves bytes behind fails, also when every run leaves the
    // same amount, as a block that the first run keeps would; so does a run
    // that takes back more than it handed out.
    #[test]
    fn a_run_that_leaves_bytes_behind_fails() {
        let mut runs = [passing(); 4];
        runs[2].left = 19;
        assert_eq!(failures(&runs), [2]);
        let leaking = Run {
            left: 19,
            ..passing()
        };
        assert_eq!(failures(&[leaking; 3]), [0, 1, 2]);
        runs[2].left = -8;
        assert_eq!(failures(&runs), [2]);
    }

    // A run without a value fails, and so does a run without a line.
    #[test]
    fn a_run_without_a_value_or_a_line_fails() {
        let mut runs = [passing(); 3];
        runs[1].value = false;
        assert_eq!(failures(&runs), [1]);
        let mut runs = [passing(); 3];
        runs[2].length = None;
        assert_eq!(failures(&runs), [2]);
        let unwritten = Run {
            length: None,
            ..passing()
        };
        assert_eq!(failures(&[unwritten; 2]), [0, 1]);
    }

    // A run whose line differs from the line of the first run fails, by its
    // length or by its checksum.
    #[test]
    fn a_run_with_another_line_fails() {
        let mut runs = [passing(); 3];
        runs[1].length = Some(13);
        runs[2].checksum = checksum(b"value\t1\t2\t4\n");
        assert_eq!(failures(&runs), [1, 2]);
    }
}
