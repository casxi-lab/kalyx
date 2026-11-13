# Resource profile

This profile records the memory that the requests of kalyx use on one host:
the heap peak of each of the 58 [answer vectors](../vectors/README.md), and
the native stack of each of them and of deep inputs at several values of
`max_depth`. It is a measurement on the host named below, not a bound that
the library guarantees; a host that runs kalyx, such as the calculator
worker that krepi plans, is to size its stack and heap from it with a
margin of its own. The context of a
request bounds work and logical sizes, not the bytes that a request
allocates or the stack it uses
([Table 2 of the command entry](components/command/contract.md#table-2-the-limits-and-who-enforces-them)).

## How it was measured

**Host.** Apple M2 Pro, 10 cores, 16 GiB of memory, macOS 26.5.2 (Darwin
25.5.0, arm64, 16 KiB pages); `rustc 1.99.0 (b940084d7 2026-09-28)` and
`cargo 1.99.0`, the toolchain of `rust-toolchain.toml`; the system
allocator.

**Tool.** The allocation check in `checks/allocation/`, the program that
`cargo xtask check` runs to show that every case of the vectors, run 100
times, leaves the live bytes of the process at their baseline
([the allocation check](components/command/contract.md#the-allocation-check)).
Run with `profile`, it prints the tables below. The profile is measured by
hand and is not part of `cargo xtask check`:

```sh
cargo run --locked --release --manifest-path checks/allocation/Cargo.toml -- profile
```

It takes about 10 seconds on the host above. The release profile of the
check, like that of the package, keeps overflow checks. The tables below
come from one build. Runs of one build can move a row by one frame, and
another build of the same source by up to two frames, 608 bytes (for
example `rational_sum_512`).

**Heap.** The counting allocator of the check adds the size of every block
that it hands out to the live bytes and subtracts the size of every block
that it takes back. For each case, the profile runs the request once as a
host does: a context with the limits of the case, `execute`, the line of
the outcome under that context, and for an error whose line does not fit,
the line under a fresh context. The heap peak is the largest number of live
bytes above the level before the run, and the blocks are those that the run
allocates. The allocation check measures the same peaks in its 5,800 runs
of these cases and reports the largest, 901,176 bytes.

**Stack.** The stack is measured without `unsafe` code in the package or in
the check. The program runs the request again in a child process, on a
thread with a stack of 1 MiB, below a number of padding frames that fill
the stack first. Each padding frame holds a buffer of 256 bytes and takes
304 bytes of stack on this host, the mean distance between the buffers of
the first and the last frame. A bisection finds the most padding frames
under which the child still exits normally; a stack overflow ends it with a
signal. That number is then lowered until ten runs in a row complete, since
one run can use a frame or two more than another when the system allocator
takes a longer path. The stack of a request is the number of padding frames
that it displaces, compared with a thread that runs nothing, times 304
bytes. The figure is within one frame, 304 bytes, of what one run
measures, and includes the frames of the check that run the request and those of the
system allocator. A thread that asks for 1 MiB and runs nothing holds
3,484 padding frames, 1,059,136 bytes: the thread has somewhat more usable
stack than it asks for, so the figures use only differences in padding
frames, never the size of the thread.

## How to read it

- **The stack does not grow with depth.** Every case uses about 4,300 to
  10,000 bytes of stack, the most for `dense_rational_64` and
  `dense_rational_128`. Inputs of 127 to 65,535 levels of parentheses use
  the same 5,776 bytes, and right-nested sums of 63 to 32,767 levels the
  same 7,296 bytes to evaluate and, within one frame, 7,600 bytes to
  differentiate: the parser, the term core and the expansion walk their
  inputs with stacks on the heap and never recurse natively
  ([traversal and drop](architecture.md#traversal-and-drop)). So the native
  stack does not depend on `max_depth`: on this host, the requests measured
  here need at most 10,032 bytes beyond the stack that a thread takes by
  itself.
- **The heap grows with depth and size.** The heap peak of a deep input
  grows linearly with its levels: 72 bytes per level of parentheses, and
  464 bytes per level of right-nested sums, which give 4.7 MB and 15.2 MB at
  `max_depth = 65536`. `max_depth`, with `max_input_bytes`, `max_nodes`
  and `max_storage_bytes`, is what bounds this part of the heap. Among the
  cases, the largest heap peak is 901,176 bytes, for `flat_sum_2048`, the
  sum of 2,048 numbers; every other case stays below 625,000 bytes, and 48
  of the 58 below 30,000 bytes.
- **Errors are cheap.** The nine error cases peak below 10,000 bytes of
  heap and use at most 7,296 bytes of stack; a request that exceeds a limit
  stops before it builds what the limit forbids.
- **A power is computed before its size is stored.** `max_integer_bits`
  bounds a power of numbers before it is computed, and its work is charged
  before it is computed too, by the machine words of the operands of its
  squarings and multiplications, as a product or a quotient of numbers is
  charged by the words of its operands. Under the default limits a number
  holds at most 4,096 bits, and `max_exponent` (4,096) rejects an exponent
  such as 4294967023 first. With both `max_exponent` and `max_integer_bits`
  raised far beyond their defaults, the charge of a power such as
  $3^{4294967023}$, about $4.7 \cdot 10^{15}$ units, exceeds the default
  `max_work`, and the power fails before it runs. With `max_work` raised as
  well, the power is computed in full before any limit can stop it: on the
  host above it was still running after more than 100 seconds when it was
  stopped. A sum, a difference, a negation, an inverse, a comparison and
  `Rational::new` charge one unit whatever the size of their operands, and
  the reduction of a fraction is not charged by its steps, so with
  `max_integer_bits` raised far beyond its default their CPU time grows
  with the size of the numbers and their work does not. A host that raises
  these limits bounds the memory and the CPU time of a request itself.
- **Other hosts differ.** Another operating system, page size, allocator or
  compiler version changes the figures, and the stack of a thread that runs
  nothing is not included. On another host, run the command above.

## The cases of the vectors

Each case runs under the limits of its `limits` column. The result is that
of the vector; blocks are the allocations of one run.

| Case | Result | Heap peak (bytes) | Blocks | Stack (bytes) |
| --- | --- | ---: | ---: | ---: |
| `rational_sum` | ok | 2544 | 39 | 8512 |
| `exact_decimal` | ok | 1016 | 25 | 8512 |
| `wide_integer` | ok | 912 | 24 | 6384 |
| `negative_power` | ok | 1368 | 29 | 7904 |
| `precedence` | ok | 2336 | 32 | 7296 |
| `binomial` | ok | 4339 | 178 | 7600 |
| `factor_product` | ok | 3500 | 154 | 7296 |
| `rational_coefficients` | ok | 2979 | 159 | 9120 |
| `derivative` | ok | 4163 | 158 | 7904 |
| `named_variable` | ok | 3211 | 123 | 8816 |
| `cancellation` | ok | 3884 | 130 | 7600 |
| `integer_product_32` | ok | 1016 | 23 | 7296 |
| `rational_sum_32` | ok | 2544 | 43 | 8512 |
| `integer_product_64` | ok | 1032 | 25 | 7296 |
| `rational_sum_64` | ok | 2544 | 48 | 8512 |
| `integer_product_128` | ok | 1088 | 28 | 7296 |
| `rational_sum_128` | ok | 2608 | 76 | 8512 |
| `integer_product_256` | ok | 1216 | 33 | 7296 |
| `rational_sum_256` | ok | 2800 | 86 | 8816 |
| `integer_product_512` | ok | 1616 | 33 | 7296 |
| `rational_sum_512` | ok | 2992 | 93 | 9120 |
| `integer_product_1024` | ok | 4224 | 71 | 7296 |
| `rational_sum_1024` | ok | 5781 | 173 | 8512 |
| `flat_sum_32` | ok | 14136 | 59 | 7296 |
| `balanced_sum_32` | ok | 10480 | 208 | 7296 |
| `flat_sum_256` | ok | 112696 | 289 | 7296 |
| `balanced_sum_256` | ok | 78576 | 1555 | 7296 |
| `flat_sum_2048` | ok | 901176 | 2087 | 7296 |
| `balanced_sum_2048` | ok | 624112 | 12311 | 7296 |
| `right_nested_16` | ok | 11312 | 119 | 7296 |
| `right_nested_63` | ok | 29784 | 404 | 7296 |
| `dense_rational_8` | ok | 6067 | 302 | 9120 |
| `derivative_8` | ok | 6347 | 238 | 7904 |
| `coefficient_cancellation_8` | ok | 3691 | 76 | 7600 |
| `dense_rational_32` | ok | 21235 | 1046 | 9120 |
| `derivative_32` | ok | 24107 | 898 | 7904 |
| `coefficient_cancellation_32` | ok | 3691 | 76 | 7600 |
| `dense_rational_64` | ok | 44891 | 9202 | 10032 |
| `derivative_64` | ok | 48555 | 1903 | 7904 |
| `coefficient_cancellation_64` | ok | 3691 | 76 | 7600 |
| `dense_rational_128` | ok | 101283 | 99163 | 10032 |
| `derivative_128` | ok | 104027 | 12526 | 8208 |
| `coefficient_cancellation_128` | ok | 3691 | 76 | 7600 |
| `dense_product_8` | ok | 14170 | 673 | 7904 |
| `dense_product_32` | ok | 55858 | 2751 | 7904 |
| `dense_product_64` | ok | 111442 | 5710 | 7904 |
| `sparse_product_8` | ok | 3267 | 136 | 7296 |
| `sparse_product_32` | ok | 3267 | 144 | 7296 |
| `sparse_product_128` | ok | 3267 | 152 | 7296 |
| `zero_division_1` | DivisionByZero | 1488 | 31 | 5776 |
| `fractional_power_1` | NonIntegerExponent | 1520 | 33 | 7296 |
| `unknown_symbol_1` | UnknownSymbol | 1771 | 47 | 7296 |
| `rational_function_1` | NotPolynomial | 3187 | 87 | 7296 |
| `degree_limit_1` | ResourceLimit | 789 | 32 | 5776 |
| `bit_limit_1` | ResourceLimit | 787 | 30 | 6080 |
| `depth_limit_1` | ResourceLimit | 9264 | 31 | 4256 |
| `right_depth_limit_1` | ResourceLimit | 3920 | 48 | 4560 |
| `invalid_syntax_1` | Syntax | 253 | 20 | 4256 |

## Deep inputs

Each input runs under `max_depth` as given and every other limit far above
what it needs; its levels are the most that `max_depth` accepts, and one
level more fails with `ResourceLimit` naming `max_depth`. `parentheses` is
`eval` of $((\ldots(1)\ldots))$, `right-sums` is `eval` of
$1+(1+(\ldots(1)\ldots))$, and `right-sums-of-x` is `diff` in $x$ of
$x+(x+(\ldots(x)\ldots))$.

| Input | `max_depth` | Levels | Result | Heap peak (bytes) | Stack (bytes) |
| --- | ---: | ---: | --- | ---: | ---: |
| parentheses | 128 | 127 | ok | 9264 | 5776 |
| parentheses | 1024 | 1023 | ok | 73776 | 5776 |
| parentheses | 8192 | 8191 | ok | 589872 | 5776 |
| parentheses | 65536 | 65535 | ok | 4718640 | 5776 |
| right-sums | 128 | 63 | ok | 29784 | 7296 |
| right-sums | 1024 | 511 | ok | 237656 | 7296 |
| right-sums | 8192 | 4095 | ok | 1900632 | 7296 |
| right-sums | 65536 | 32767 | ok | 15204440 | 7296 |
| right-sums-of-x | 128 | 63 | ok | 30289 | 7600 |
| right-sums-of-x | 1024 | 511 | ok | 238609 | 7600 |
| right-sums-of-x | 8192 | 4095 | ok | 1905169 | 7600 |
| right-sums-of-x | 65536 | 32767 | ok | 15237649 | 7904 |
