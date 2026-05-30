import Init.Data.Array.QSort.Basic
import Init.Data.Ord.String
import Examples.ReducerArgs

open LeanReducers
open Examples

namespace Examples.WordCount

structure Options where
  top : Nat := 25
  paths : Array System.FilePath := #[]
  reducer : ReducerArgs := {}

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe word_count [options] <text-file>...",
    "",
    "--top N                 show the N most common words",
    ReducerArgs.usage
  ]

private partial def parseArgs : List String -> Options -> Except String Options
  | [], opts => .ok opts
  | "--top" :: n :: rest, opts =>
      match n.toNat? with
      | some top => parseArgs rest { opts with top := top }
      | none => .error s!"--top expects a natural number, got {n}"
  | "--top" :: [], _ =>
      .error "--top expects a natural number"
  | args, opts => do
      match ← ReducerArgs.parse? args opts.reducer with
      | some (rest, reducer) => parseArgs rest { opts with reducer := reducer }
      | none =>
          match args with
          | arg :: rest =>
              if arg.startsWith "--" then
                .error s!"unknown option: {arg}"
              else
                parseArgs rest { opts with paths := opts.paths.push arg }
          | [] => .ok opts

private structure TokenState (ρ : Type) where
  current : String
  apply : ρ → ρ

private def flushToken (step : String → ρ → ρ) (state : TokenState ρ) : TokenState ρ :=
  if state.current.isEmpty then
    state
  else
    { current := "", apply := fun acc => state.apply (step state.current acc) }

private def wordsOfLine (line : String) : ReducerSeq String where
  run := fun unit step =>
    let state :=
      line.foldl
        (fun state c =>
          if c.isAlphanum then
            { state with current := state.current.push c.toLower }
          else
            flushToken step state)
        { current := "", apply := id }
    (flushToken step state).apply unit

private def wordCounts (cfg : Config) (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  ReducerPar.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupByWithConfig cfg (MonoidSpec.additive Nat) id (fun _ count => count + 1)

private def wordCountsSequential (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  ReducerSeq.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupBy 0 id (fun _ count => count + 1)

private def wordLess (left right : String × Nat) : Bool :=
  if left.snd == right.snd then
    match compare left.fst right.fst with
    | Ordering.lt => true
    | _ => false
  else
    right.snd < left.snd

private def spaces (n : Nat) : String :=
  "".pushn ' ' n

private def dashes (n : Nat) : String :=
  "".pushn '-' n

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
  if opts.reducer.help then
    IO.println usage
  else if opts.paths.isEmpty then
    IO.eprintln "missing input file"
    IO.eprintln usage
    IO.Process.exit 1
  else
    checkInputPaths opts.paths
    match opts.reducer.validate with
    | .error message =>
        IO.eprintln message
        IO.Process.exit 1
    | .ok () => pure ()
    let startMs ← IO.monoMsNow
    let (implementation, counts) ←
      if opts.reducer.baseline then
        pure ("sequential reducer", ← wordCountsSequential opts.paths)
      else
        let cfg := opts.reducer.config
        let name :=
          if cfg.maxDepth == 0 then
            s!"sequential reducer (maxDepth {cfg.maxDepth})"
          else
            s!"parallel reducer (maxDepth {cfg.maxDepth})"
        pure (name, ← wordCounts cfg opts.paths)
    let elapsedMs := (← IO.monoMsNow) - startMs
    printTop opts.paths opts.top implementation elapsedMs counts

end Examples.WordCount

def main (args : List String) : IO Unit :=
  Examples.WordCount.main args
