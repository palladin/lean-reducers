import Init.System.IO

namespace Examples.FetchWikiText

structure Options where
  dataDir : System.FilePath := "Examples/data"
  url : String := "https://data.deepai.org/wikitext-103.zip"
  force : Bool := false

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe fetch_wikitext103 [--data-dir DIR] [--url URL] [--force]",
    "",
    "Downloads a WikiText-103 zip and extracts plain text files under DIR/wikitext-103.",
    "Requires curl and unzip on PATH."
  ]

private def parseArgs : List String -> Options -> Except String Options
  | [], opts => .ok opts
  | "--data-dir" :: dir :: rest, opts =>
      parseArgs rest { opts with dataDir := dir }
  | "--data-dir" :: [], _ =>
      .error "--data-dir expects a directory"
  | "--url" :: url :: rest, opts =>
      parseArgs rest { opts with url := url }
  | "--url" :: [], _ =>
      .error "--url expects a URL"
  | "--force" :: rest, opts =>
      parseArgs rest { opts with force := true }
  | "--help" :: _, opts =>
      .ok opts
  | arg :: _, _ =>
      .error s!"unknown argument: {arg}"

private def runCommand (cmd : String) (args : Array String) : IO Unit := do
  IO.println s!"$ {String.intercalate " " (cmd :: args.toList)}"
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    stdin := .null
    stdout := .inherit
    stderr := .inherit
  }
  let code ← child.wait
  if code != 0 then
    throw <| IO.userError s!"process '{cmd}' exited with code {code}"

private def tokenFiles (dataDir : System.FilePath) : Array System.FilePath :=
  let dir := dataDir / "wikitext-103"
  #[dir / "wiki.train.tokens", dir / "wiki.valid.tokens", dir / "wiki.test.tokens"]

private def csvFiles (dataDir : System.FilePath) : Array System.FilePath :=
  let dir := dataDir / "wikitext-103"
  #[dir / "train.csv", dir / "test.csv"]

private def existingFiles (paths : Array System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for path in paths do
    if ← path.pathExists then
      found := found.push path
  pure found

private def usableFiles (dataDir : System.FilePath) : IO (Array System.FilePath) := do
  let tokens ← existingFiles (tokenFiles dataDir)
  if !tokens.isEmpty then
    pure tokens
  else
    existingFiles (csvFiles dataDir)

private def prepared (dataDir : System.FilePath) : IO Bool := do
  pure (!(← usableFiles dataDir).isEmpty)

private def printOutputs (dataDir : System.FilePath) : IO Unit := do
  let files ← usableFiles dataDir
  if files.isEmpty then
    IO.eprintln s!"no recognized WikiText-103 files found under {dataDir / "wikitext-103"}"
    IO.eprintln "expected either wiki.*.tokens files or train.csv/test.csv"
    IO.Process.exit 1
  IO.println "WikiText-103 files:"
  for path in files do
    IO.println s!"  {path}"
  if files.any (fun path => path.toString.endsWith ".csv") then
    IO.println ""
    IO.println s!"Run: lake exe word_count --top 25 {dataDir / "wikitext-103" / "train.csv"}"

def main (args : List String) : IO Unit := do
  let opts ←
    match parseArgs args {} with
    | .ok opts => pure opts
    | .error message => do
        IO.eprintln message
        IO.eprintln usage
        throw (IO.userError message)
  if args.contains "--help" then
    IO.println usage
  else if (← prepared opts.dataDir) && !opts.force then
    IO.println s!"WikiText-103 is already prepared under {opts.dataDir}."
    printOutputs opts.dataDir
  else
    IO.FS.createDirAll opts.dataDir
    let zipPath := opts.dataDir / "wikitext-103.zip"
    if opts.force || !(← zipPath.pathExists) then
      runCommand "curl" #["-L", "--fail", "-o", toString zipPath, opts.url]
    else
      IO.println s!"Using existing archive {zipPath}."
    runCommand "unzip" #["-q", "-o", toString zipPath, "-d", toString opts.dataDir]
    printOutputs opts.dataDir

end Examples.FetchWikiText

def main (args : List String) : IO Unit :=
  Examples.FetchWikiText.main args
