import Init.Data.Array.QSort.Basic
import Init.Data.Ord.String
import Std.Data.HashMap.Basic
import LeanReducers

open LeanReducers

namespace Examples.WordCount

structure Options where
  top : Nat := 25
  paths : Array System.FilePath := #[]
  diagnostics : DiagnosticsConfig := {}
  baseline : Bool := false

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe word_count [--top N] [--baseline] [--diagnostics] [--diagnostics-output console|stderr|stdout] <text-file>...",
    "",
    "--baseline              run a simple sequential baseline implementation",
    "--diagnostics           show a colorized top-anchored diagnostics panel with per-CPU bars",
    "--diagnostics-output    choose where the diagnostics panel is emitted"
  ]

private def withDiagnostics (opts : Options) : Options :=
  { opts with diagnostics := { opts.diagnostics with enabled := true, sampleSystem := true } }

private def withDiagnosticsOutput (opts : Options) (output : DiagnosticsOutput) : Options :=
  { opts with diagnostics := { opts.diagnostics with output := output } }

private def parseArgs : List String -> Options -> Except String Options
  | [], opts => .ok opts
  | "--top" :: n :: rest, opts =>
      match n.toNat? with
      | some top => parseArgs rest { opts with top := top }
      | none => .error s!"--top expects a natural number, got {n}"
  | "--top" :: [], _ =>
      .error "--top expects a natural number"
  | "--baseline" :: rest, opts =>
      parseArgs rest { opts with baseline := true }
  | "--diagnostics" :: rest, opts =>
      parseArgs rest (withDiagnostics opts)
  | "--diagnostics-output" :: "console" :: rest, opts =>
      parseArgs rest (withDiagnosticsOutput opts DiagnosticsOutput.console)
  | "--diagnostics-output" :: "stderr" :: rest, opts =>
      parseArgs rest (withDiagnosticsOutput opts DiagnosticsOutput.stderr)
  | "--diagnostics-output" :: "stdout" :: rest, opts =>
      parseArgs rest (withDiagnosticsOutput opts DiagnosticsOutput.stdout)
  | "--diagnostics-output" :: value :: _, _ =>
      .error s!"--diagnostics-output expects console, stderr, or stdout, got {value}"
  | "--diagnostics-output" :: [], _ =>
      .error "--diagnostics-output expects console, stderr, or stdout"
  | "--help" :: _, opts =>
      .ok opts
  | arg :: rest, opts =>
      parseArgs rest { opts with paths := opts.paths.push arg }

private structure TokenState where
  words : Array String
  current : String

private def flushToken (state : TokenState) : TokenState :=
  if state.current.isEmpty then
    state
  else
    { words := state.words.push state.current, current := "" }

private def wordsOfLine (line : String) : Array String :=
  let state :=
    line.foldl
      (fun state c =>
        if c.isAlphanum then
          { state with current := state.current.push c.toLower }
        else
          flushToken state)
      { words := #[], current := "" }
  (flushToken state).words

private def wordCounts (cfg : Config) (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  Reducer.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupByWithConfig cfg (MonoidSpec.additive Nat) id (fun _ count => count + 1)

private def addWord (counts : Std.HashMap String Nat) (word : String) : Std.HashMap String Nat :=
  counts.insert word (counts.getD word 0 + 1)

private def addLineWords (counts : Std.HashMap String Nat) (line : String) : Std.HashMap String Nat :=
  (wordsOfLine line).foldl addWord counts

partial def countHandleSequential (handle : IO.FS.Handle)
    (counts : Std.HashMap String Nat) : IO (Std.HashMap String Nat) := do
  let line ← handle.getLine
  if line.isEmpty then
    pure counts
  else
    countHandleSequential handle (addLineWords counts line)

private def wordCountsBaseline (paths : Array System.FilePath) : IO (Array (String × Nat)) := do
  let mut counts : Std.HashMap String Nat := {}
  for path in paths do
    counts ← IO.FS.withFile path IO.FS.Mode.read fun handle =>
      countHandleSequential handle counts
  pure counts.toArray

private def wordLess (left right : String × Nat) : Bool :=
  if left.snd == right.snd then
    match compare left.fst right.fst with
    | Ordering.lt => true
    | _ => false
  else
    right.snd < left.snd

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private def dashes (n : Nat) : String :=
  String.ofList (List.replicate n '-')

private def padLeft (width : Nat) (s : String) : String :=
  spaces (width - s.length) ++ s

private def natWidth (n : Nat) : Nat :=
  (toString n).length

private def maxCountWidth (rows : Array (String × Nat)) : Nat :=
  rows.foldl (fun width row => Nat.max width (natWidth row.snd)) "count".length

private def totalWords (counts : Array (String × Nat)) : Nat :=
  counts.foldl (fun total row => total + row.snd) 0

private def formatTenths (n : Nat) : String :=
  s!"{n / 10}.{n % 10}"

private def secondsTenths (ms : Nat) : Nat :=
  ms / 100

private def printTop (paths : Array System.FilePath) (top : Nat)
    (implementation : String) (elapsedMs : Nat) (counts : Array (String × Nat)) : IO Unit := do
  let rows := (counts.qsort wordLess).take top
  let rankWidth := Nat.max "rank".length (natWidth rows.size)
  let countWidth := maxCountWidth rows
  IO.println "Word count"
  IO.println s!"implementation: {implementation}"
  IO.println s!"files: {paths.size}"
  IO.println s!"elapsed: {formatTenths (secondsTenths elapsedMs)}s"
  IO.println s!"words: {totalWords counts}"
  IO.println s!"unique words: {counts.size}"
  IO.println s!"shown: {rows.size}"
  IO.println ""
  IO.println s!"{padLeft rankWidth "rank"}  {padLeft countWidth "count"}  word"
  IO.println s!"{dashes rankWidth}  {dashes countWidth}  ----"
  let mut rank := 1
  for row in rows do
    IO.println s!"{padLeft rankWidth (toString rank)}  {padLeft countWidth (toString row.snd)}  {row.fst}"
    rank := rank + 1

private def checkInputPaths (paths : Array System.FilePath) : IO Unit := do
  for path in paths do
    if !(← path.pathExists) then
      IO.eprintln s!"missing input file: {path}"
      if toString path == "Examples/data/wikitext-103/wiki.train.tokens" then
        IO.eprintln "prepare WikiText-103 with: lake exe fetch_wikitext103"
        IO.eprintln "the default mirror extracts to: Examples/data/wikitext-103/train.csv"
      IO.Process.exit 1

def main (args : List String) : IO Unit := do
  let opts ←
    match parseArgs args {} with
    | .ok opts => pure opts
    | .error message => do
        IO.eprintln message
        IO.eprintln usage
        IO.Process.exit 1
  if args.contains "--help" then
    IO.println usage
  else if opts.paths.isEmpty then
    IO.eprintln "missing input file"
    IO.eprintln usage
    IO.Process.exit 1
  else
    checkInputPaths opts.paths
    if opts.baseline && opts.diagnostics.enabled then
      IO.eprintln "--diagnostics is only available for the reducer implementation"
      IO.Process.exit 1
    let startMs ← IO.monoMsNow
    let (implementation, counts) ←
      if opts.baseline then
        pure ("sequential baseline", ← wordCountsBaseline opts.paths)
      else
        let cfg : Config := { Config.default with diagnostics := opts.diagnostics }
        pure ("parallel reducer", ← wordCounts cfg opts.paths)
    let elapsedMs := (← IO.monoMsNow) - startMs
    printTop opts.paths opts.top implementation elapsedMs counts

end Examples.WordCount

def main (args : List String) : IO Unit :=
  Examples.WordCount.main args
