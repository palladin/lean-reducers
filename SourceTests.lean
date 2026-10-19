import LeanReducers
import Std.Sync.Mutex

open LeanReducers

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  check failed message

private def source (text : String) : ByteSource :=
  let bytes := text.toUTF8
  { size := bytes.size, read := fun offset count => pure (bytes.extract offset (offset + count)) }

private def collect (xs : ReducerParIO String) (cfg : Config) : IO (List String) :=
  xs.reduceWithoutLaws [] (· ++ ·) (· :: ·) cfg

def main : IO Unit := do
  let samples := #["", "a", "\n", "\n\n", "αβ\n\n終わり\n", "a\r\nb\r\n", "abc\ndef",
    "begin\n" ++ String.ofList (List.replicate 4097 'x') ++ "\nend\n"]
  for text in samples do
    let input := source text
    for width in [1, 2, 3, 7, 97, 8192] do
      let ranges := ByteRange.partition #[⟨input, 0, input.size⟩] width
      for cpus in [1, 2, 4] do
        let cfg := Config.forCPUs cpus { grain := 3, maxReadBytes := 71 }
        let actual ← collect (ReducerPar.readSourceRanges ranges) cfg
        check (actual == text.splitOn "\n") s!"Partition changed line order: {text.take 20}, width {width}, cpus {cpus}"
  -- A source adapter and a local file have identical empty/trailing-line rules.
  IO.FS.withTempFile fun handle path => do
    let text := "alpha\nβeta\nlast\n"
    handle.putStr text; handle.flush
    let cfg := Config.forCPUs 4 { grain := 2, maxReadBytes := 3 }
    check ((← collect (ReducerPar.readLines path) cfg) ==
      (← collect (ReducerPar.readSources #[source text]) cfg)) "Local/remote reader divergence"
    check ((← collect (ReducerPar.readSources #[source text] false) cfg) ==
      ["alpha", "βeta", "last"]) "Trailing newline policy"
  let cfg : Config := { grain := 1, maxDepth := 2, maxReadBytes := 4, maxLineBytes := 8 }
  rejects (collect (ReducerPar.readSources #[source "123456789\n"]) cfg) "Oversized line accepted"
  let short : ByteSource := { size := 10, read := fun _ _ => pure ByteArray.empty }
  rejects (collect (ReducerPar.readSources #[short]) cfg) "Short read accepted"
  let bad : ByteSource := { size := 1, read := fun _ count => pure (if count == 0 then {} else ⟨#[255]⟩) }
  rejects (collect (ReducerPar.readSources #[bad]) cfg) "Invalid UTF-8 accepted"
  let checked := (ReducerPar.readSources #[source "1\nbad\n2"] false).tryMap fun s =>
    match s.toNat? with | some n => .ok n | none => .error s!"Invalid number: {s}"
  rejects checked.sum "Parser error disappeared"
  -- A failing left subtree must still join a slow right subtree.
  let finished ← IO.mkRef false
  let left : ByteSource := { size := 2, read := fun _ _ => throw (IO.userError "left failed") }
  let right : ByteSource := { size := 2, read := fun offset count => do
    IO.sleep 30
    finished.set true
    return ("r\n".toUTF8.extract offset (offset + count)) }
  rejects (collect (ReducerPar.readSources #[left, right]) { grain := 1, maxDepth := 1 }) "Read failure lost"
  check (← finished.get) "Reader returned with a live sibling task"
  let state ← Std.Mutex.new (0, 0, 0)
  let results ← mapTasks 3 (Array.range 12) fun i => do
    state.atomically do modify fun (active, peak, done) => (active + 1, max peak (active + 1), done)
    IO.sleep 2
    state.atomically do modify fun (active, peak, done) => (active - 1, peak, done + 1)
    return i
  let (active, peak, done) ← state.atomically get
  check (results == Array.range 12 && active == 0 && peak ≤ 3 && done == 12) "IO task budget/order"
  let finished ← IO.mkRef false
  rejects (mapTasks 2 #[0, 1] fun i => do
    if i == 0 then throw (IO.userError "failed")
    IO.sleep 30; finished.set true; return i) "IO failure lost"
  check (← finished.get) "IO map returned with a live sibling task"
  IO.println "PASS seekable sources, byte partitioning, UTF-8, bounds, parsing, task budgets and failure draining"
