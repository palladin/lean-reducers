# LeanReducers

Fused sequential and parallel reducers for Lean 4.

`LeanReducers` provides two explicit pipeline modes:

- `ReducerSeq` is the lightweight sequential API. Its core terminal is
  `reduce unit step`; it does not require algebraic proofs or parallel config.
- `ReducerPar` is the parallel API. It uses Lean's `Task`, and its lawful
  terminals accept a `MonoidSpec` so chunk results can be combined safely.

Both modes fuse transforms into the terminal reduction instead of allocating
intermediate pipeline collections.

## Quick Start

```lean
import LeanReducers

open LeanReducers

#eval
  #[(1 : Nat), 2, 3, 4]
    |> ReducerSeq.ofArray
    |>.map (fun x => x + 1)
    |>.filter (fun x => x % 2 == 0)
    |>.sum
-- 6
```

Opt into parallel reduction when the workload warrants it:

```lean
#eval
  #[(1 : Nat), 2, 3, 4]
    |> ReducerPar.ofArray
    |>.reduceWithLaws (MonoidSpec.additive Nat) (fun x acc => x + acc)
-- 10
```

Build and run the test executable:

```sh
lake build
lake exe lean_reducers_tests
```

The test executable uses Plausible to generate arrays, file contents, and
parallel configurations. Each test compares a reducer pipeline against a
sequential Lean model of the same producer, transforms, and terminal.

### Native Backend And Interpreted Runs

`ReducerPar` line-oriented file producers use a small native `pread` bridge in
compiled code. The normal path is to run through a Lake executable, as above.

If you run a file through Lean's interpreter, load the generated dynamic
libraries explicitly:

```sh
lake build LeanReducers:shared
lake env lean \
  --load-dynlib .lake/build/lib/libleanreducersio.dylib \
  --load-dynlib .lake/build/lib/liblean__reducers_LeanReducers.dylib \
  --run Test.lean
```

On Linux, use the generated `.so` files instead of `.dylib`.

## Pipeline Model

Reducers are built as a three-stage pipeline:

```lean
producer |> intermediate |> intermediate |> terminal
```

- A producer chooses sequential or parallel execution and the effect.
  `ReducerSeq.ofArray` creates a pure `ReducerSeq α`;
  `ReducerPar.readLines` creates an effectful `ReducerParIO String`.
- Intermediate operations such as `map`, `filter`, and `flatMap` transform the
  reducer without running it. They are fused into the terminal reduction plan
  instead of allocating intermediate collections.
- A terminal runs the reduction. `ReducerSeq.reduce` only needs a unit and local
  step. `ReducerPar.reduceWithLaws` additionally accepts a lawful chunk combiner.
  Convenience terminals such as `toArray`, `length`, `sum`, `min?`, `max?`,
  `avgFloat`, and `groupBy` are available in both modes.

For example:

```lean
#[(1 : Nat), 2, 3, 4] -- source data
  |> ReducerSeq.ofArray  -- producer
  |>.map (fun x => x + 1) -- intermediate
  |>.filter (fun x => x % 2 == 0) -- intermediate
  |>.sum -- terminal
```

## Core Types

```lean
structure ReducerSeqM (m : Type → Type) (α : Type)

abbrev ReducerSeq (α : Type) := ReducerSeqM Id α
abbrev ReducerSeqIO (α : Type) := ReducerSeqM IO α

structure MonoidSpec (α : Type) where
  unit : α
  combine : α → α → α
  assoc : ∀ a b c, combine (combine a b) c = combine a (combine b c)
  left_unit : ∀ a, combine unit a = a
  right_unit : ∀ a, combine a unit = a

structure ReducerParM (m : Type → Type) (α : Type)

abbrev ReducerPar (α : Type) := ReducerParM Id α
abbrev ReducerParIO (α : Type) := ReducerParM IO α
```

The `M` types carry the producer effect. Pure aliases use `Id`; file producers
return the `IO` aliases.

Internally, `ReducerSeq` producers run the fused step directly. `ReducerPar`
array producers use a pure `Task` tree. Parallel line producers use IO tasks that
read byte ranges and repair newline boundaries before folding lines.

## API Overview

Both modes expose `ofArray`, `ofArrayM`, `readFile`, `readLines`,
`readLinesFromFiles`, `readLinesFromFilesWithPath`, and `readChars` producers.
Both also expose fused `map`, `filter`, and `flatMap` transforms.

`flatMap` receives a pure sequential reducer for each input:

```lean
.flatMap : ReducerSeqM m α → (α → ReducerSeq β) → ReducerSeqM m β
.flatMap : ReducerParM m α → (α → ReducerSeq β) → ReducerParM m β
```

The inner `ReducerSeq` is an allocation-free expansion plan. It is consumed
inside the outer reduction; it does not introduce nested effects or parallel
task trees. Build small expansions with `ReducerSeq.empty`, `one`, and `append`,
or wrap an existing collection with `ReducerSeq.ofArray` or `ofList`.

### Sequential Terminals

```lean
.reduce    : ρ → (α → ρ → ρ) → ReducerSeqM m α → m ρ
.reduceMap : ρ → (ρ → ρ → ρ) → (α → ρ) → ReducerSeqM m α → m ρ
.groupBy   : ν → (α → κ) → (α → ν → ν) → ReducerSeqM m α → m (Array (κ × ν))
```

`ReducerSeq` convenience terminals include `toArray`, `length`, `sum`,
`sumFloat`, `min?`, `max?`, `avgFloat`, and `avg`. Sequential `.sum` only needs
`Add α` and `OfNat α 0`; it can be used directly with `Float`.

### Parallel Terminals

```lean
.reduceWithLaws    : MonoidSpec ρ → (α → ρ → ρ) → ReducerParM m α → m ρ
.reduceMapWithLaws : MonoidSpec ρ → (α → ρ) → ReducerParM m α → m ρ
.reduceWithoutLaws : ρ → (ρ → ρ → ρ) → (α → ρ → ρ) → ReducerParM m α → m ρ
.groupBy           : MonoidSpec ν → (α → κ) → (α → ν → ν) → ReducerParM m α →
  m (Array (κ × ν))
```

`ReducerPar` exposes the same convenience terminal names. Parallel `.sum`
requires `LawfulAddMonoid α`; practical floating-point reductions use
`.sumFloat`.

For pure reducers, `m` is `Id`, so terminals return values directly. For file
producers, terminals return `IO`. `min?`, `max?`, and floating averages return
`none` for empty reducers. Pure reducers in both modes also expose proof-bearing
`.min` and `.max`.

Grouped values start at the supplied unit, then the per-key step is applied for
each element. Parallel grouping receives its unit and chunk combiner through
`MonoidSpec`. Group output order is unspecified.

## Examples

### `flatMap`

```lean
#eval
  #[1, 2, 3]
    |> ReducerSeq.ofArray
    |>.flatMap (fun x =>
      ReducerSeq.one x
        |>.append (ReducerSeq.one (x * 10)))
    |>.sum
-- 66
```

### Convenience Terminals

```lean
#eval
  #[3, 1, 4, 1, 5]
    |> ReducerSeq.ofArray
    |>.min?
-- some 1

#eval
  match (#[3.0, 1.0, 4.0] |> ReducerSeq.ofArray |>.avgFloat) with
  | some avg => avg > 2.0 && avg < 3.0
  | none => false
-- true
```

### `groupBy`

```lean
#eval
  #[("a", 1), ("b", 2), ("a", 3)]
    |> ReducerPar.ofArray
    |>.groupBy
      (MonoidSpec.additive Nat)
      (fun row => row.1)
      (fun row acc => row.2 + acc)
    |>.qsort (fun left right => compare left.1 right.1 == Ordering.lt)
-- #[("a", 4), ("b", 2)]
```

### File Producers

`ReducerSeq.readLines` reads and reduces lines sequentially without exposing
parallel tuning knobs. Multi-file sequential producers process one file at a
time.

`ReducerPar.readLines` is the large-file path: it splits the file into byte ranges,
reads those ranges in parallel, then adjusts each range to whole-line boundaries
so every line is folded exactly once.

`ReducerPar.readLinesFromFiles` and `ReducerPar.readLinesFromFilesWithPath` use the
same source byte-range scheduler as `ReducerPar.readLines`, so skewed file sizes can
be balanced by splitting large files into multiple ranges.

Because these producers use the native backend in compiled code, interpreted
`lean --run` sessions need the dynamic libraries described above.

```lean
def countLinesByLength (path : System.FilePath) : IO (Array (Nat × Nat)) := do
  ReducerPar.readLines path
    |>.filter (fun line => line != "")
    |>.groupBy
      (MonoidSpec.additive Nat)
      String.length
      (fun _ acc => 1 + acc)
```

Use `readLinesFromFilesWithPath` when the terminal needs to know which file
produced each line:

```lean
def countNonemptyLinesByFile
    (paths : Array System.FilePath) : IO (Array (System.FilePath × Nat)) := do
  ReducerPar.readLinesFromFilesWithPath paths
    |>.filter (fun row => row.2 != "")
    |>.groupBy
      (MonoidSpec.additive Nat)
      (fun row => row.1)
      (fun _ acc => 1 + acc)
```

## Lawfulness

`ReducerPar` can regroup chunk results. That is why its lawful reductions use
`MonoidSpec`: the result combiner must be associative and must have a lawful
unit. `ReducerSeq` does not regroup work and therefore does not require these
proofs.

Use `reduceWithoutLaws` when you have a useful `unit` and `combine` but do not want
to provide monoid proofs. The reduction still runs in parallel, so the supplied
combiner should be stable under regrouping if you need deterministic equality
with a sequential fold.

`Float` is intentionally not a lawful `.sum` target. IEEE floating-point
addition is not mathematically associative, so the library exposes:

```lean
sumFloat : ReducerPar Float → Float
avgFloat : ReducerPar Float → Option Float
```

and the monadic equivalents for practical floating-point reductions over the
without-laws reduction path.

Likewise, `min?` and `max?` use the `Min` and `Max` classes. For
parallel-stable results, those operations should behave consistently under
regrouping.

## Parallel Configuration

```lean
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
  diagnostics : DiagnosticsConfig := {}
```

Use `ReducerPar.reduceWithLawsWithConfig`, `reduceMapWithLawsWithConfig`,
`reduceWithoutLawsWithConfig`, or `groupByWithConfig` to tune parallel splitting.
For parallel line readers, `grain` is interpreted as a target byte chunk size
before newline-boundary repair.
Diagnostics are disabled by default; line readers can emit a colorized,
top-anchored panel with progress, OS-sampled process IO throughput, OS-sampled
per-CPU bars, and OS-sampled process memory through a parameterized output sink.
The default sink is `DiagnosticsOutput.console`. `cpuBars := 0` means
auto-detect the CPU count.

## Design Notes

- `ReducerSeq` line producers read one file at a time. `ReducerPar` array
  producers use index-based chunking, and parallel line readers use a small native
  `pread` bridge for true parallel range reads.
- Parallel line producers schedule over source byte ranges. Single-file reads
  start from one range, while multi-file reads start from one range per file and
  may split a large file into multiple ranges.
- File line chunks are expanded or trimmed at newline boundaries. A line that
  starts exactly at a split belongs to the right chunk, so boundary lines are not
  duplicated.
- Sequential line producers, `readFile`, and `readChars` read whole files before
  reducing.
- `map`, `filter`, and `flatMap` are fused by rewriting the terminal reduction plan;
  they do not build intermediate pipeline collections.
- `groupBy` uses a `Std.HashMap` accumulator internally and returns an
  `Array (key × value)` at the API boundary.
