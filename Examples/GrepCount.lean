import Examples.ReducerArgs

open LeanReducers
open Examples

namespace Examples.GrepCount

structure Options where
  pattern : Option String := none
  paths : Array System.FilePath := #[]
  reducer : ReducerArgs := {}

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe grep_count [options] <pattern> <text-file>...",
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
                match opts.pattern with
                | none => parseArgs rest { opts with pattern := some arg }
                | some _ => parseArgs rest { opts with paths := opts.paths.push (System.FilePath.mk arg) }
          | [] => .ok opts

private def grepCountParallel (opts : Options) (pattern : String) : IO Nat := do
  ReducerPar.readLinesFromFiles opts.paths
    |>.filter (fun line => line.contains pattern)
    |>.reduceMapWithLawsWithConfig opts.reducer.config (MonoidSpec.additive Nat) (fun _ => 1)

private def grepCountSequential (opts : Options) (pattern : String) : IO Nat :=
  ReducerSeq.readLinesFromFiles opts.paths
    |>.filter (fun line => line.contains pattern)
    |>.reduceMap 0 (fun left right => left + right) (fun _ => 1)

private def formatTenths (n : Nat) : String :=
  s!"{n / 10}.{n % 10}"

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
  else match opts.pattern with
  | none =>
      IO.eprintln usage
      IO.Process.exit 1
  | some pattern =>
      if pattern.isEmpty then
        IO.eprintln "pattern must not be empty"
        IO.Process.exit 1
      else if opts.paths.isEmpty then
        IO.eprintln usage
        IO.Process.exit 1
      else
        match opts.reducer.validate with
        | .error message =>
            IO.eprintln message
            IO.Process.exit 1
        | .ok () => pure ()
        let startMs ← IO.monoMsNow
        let (implementation, count) ←
          if opts.reducer.baseline then
            pure ("sequential ReducerSeq baseline", ← grepCountSequential opts pattern)
          else
            pure ("parallel ReducerPar", ← grepCountParallel opts pattern)
        let elapsedMs := (← IO.monoMsNow) - startMs
        IO.println "Grep count"
        IO.println s!"implementation: {implementation}"
        IO.println s!"files: {opts.paths.size}"
        IO.println s!"elapsed: {formatTenths (elapsedMs / 100)}s"
        IO.println s!"matches: {count}"

end Examples.GrepCount

def main (args : List String) : IO Unit :=
  Examples.GrepCount.main args
