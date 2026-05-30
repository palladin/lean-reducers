import Examples.ReducerArgs

open LeanReducers
open Examples

namespace Examples.LineCount

structure Options where
  paths : Array System.FilePath := #[]
  reducer : ReducerArgs := {}

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe line_count [options] <text-file>...",
    "",
    ReducerArgs.usage
  ]

private partial def parseArgs : List String → Options → Except String Options
  | [], opts => .ok opts
  | args, opts => do
      match ← ReducerArgs.parse? args opts.reducer with
      | some (rest, reducer) => parseArgs rest { opts with reducer := reducer }
      | none =>
          match args with
          | arg :: rest =>
              if arg.startsWith "--" then
                .error s!"unknown option: {arg}"
              else
                parseArgs rest { opts with paths := opts.paths.push (System.FilePath.mk arg) }
          | [] => .ok opts

private def lineCountParallel (opts : Options) : IO Nat := do
  ReducerPar.readLinesFromFiles opts.paths
    |>.reduceMapWithLawsWithConfig opts.reducer.config (MonoidSpec.additive Nat) (fun _ => 1)

private def lineCountSequential (opts : Options) : IO Nat :=
  ReducerSeq.readLinesFromFiles opts.paths
    |>.length

def main (args : List String) : IO Unit := do
  let opts ←
    match parseArgs args {} with
    | .ok opts => pure opts
    | .error message => do
        IO.eprintln message
        IO.eprintln usage
        IO.Process.exit 1
  if opts.reducer.help then
    IO.println usage
  else if opts.paths.isEmpty then
    IO.eprintln usage
    IO.Process.exit 1
  else
    match opts.reducer.validate with
    | .error message =>
        IO.eprintln message
        IO.Process.exit 1
    | .ok () => pure ()
    if opts.reducer.baseline then
      IO.println (← lineCountSequential opts)
    else
      IO.println (← lineCountParallel opts)

end Examples.LineCount

def main (args : List String) : IO Unit :=
  Examples.LineCount.main args
