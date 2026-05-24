import Init.Data.Array.QSort.Basic
import Init.Data.Ord.String
import LeanReducers

open LeanReducers

namespace Examples.WordCount

structure Options where
  top : Nat := 25
  paths : Array System.FilePath := #[]

private def usage : String :=
  "Usage: lake exe word_count [--top N] <text-file>..."

private def parseArgs : List String -> Options -> Except String Options
  | [], opts => .ok opts
  | "--top" :: n :: rest, opts =>
      match n.toNat? with
      | some top => parseArgs rest { opts with top := top }
      | none => .error s!"--top expects a natural number, got {n}"
  | "--top" :: [], _ =>
      .error "--top expects a natural number"
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

private def wordCounts (paths : Array System.FilePath) : IO (Array (String × Nat)) :=
  Reducer.readLinesFromFiles paths
    |>.flatMap wordsOfLine
    |>.groupBy (MonoidSpec.additive Nat) id (fun _ count => count + 1)

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

private def printTop (paths : Array System.FilePath) (top : Nat)
    (counts : Array (String × Nat)) : IO Unit := do
  let rows := (counts.qsort wordLess).take top
  let rankWidth := Nat.max "rank".length (natWidth rows.size)
  let countWidth := maxCountWidth rows
  IO.println "Word count"
  IO.println s!"files: {paths.size}"
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
    let counts ← wordCounts opts.paths
    printTop opts.paths opts.top counts

end Examples.WordCount

def main (args : List String) : IO Unit :=
  Examples.WordCount.main args
