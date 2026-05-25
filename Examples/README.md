# Examples

## Word Count

`word_count` is a small executable that counts normalized ASCII words across one
or more text files. It is meant to exercise the reducer path that matters for
large text workloads:

```lean
Reducer.readLinesFromFiles paths
  |>.flatMap wordsOfLine
  |>.groupBy (MonoidSpec.additive Nat) id (fun _ count => count + 1)
```

Run the bundled smoke sample:

```sh
lake exe word_count --top 10 Examples/sample/wiki.train.sample.txt
```

For a larger demo, download and extract WikiText-103 into plain text files:

```sh
lake exe fetch_wikitext103
lake exe word_count --top 25 Examples/data/wikitext-103/train.csv
```

Run a simple sequential baseline over the same input:

```sh
lake exe word_count --baseline --top 25 Examples/data/wikitext-103/train.csv
```

Show the colorized, top-anchored diagnostics panel with per-CPU bars while it
runs:

```sh
lake exe word_count --diagnostics --top 25 Examples/data/wikitext-103/train.csv
```

The diagnostic output defaults to the console and can be routed explicitly:

```sh
lake exe word_count --diagnostics --diagnostics-output stdout --top 25 Examples/data/wikitext-103/train.csv
```

CPU bars are sampled from the OS per-core counters, and the CPU bar count is
auto-detected. Memory and IO are sampled from OS process counters. Progress is
still measured inside the line-range scheduler.

The fetcher is Lean code that shells out to `curl` and `unzip`, and writes:

- `Examples/data/wikitext-103/train.csv`
- `Examples/data/wikitext-103/test.csv`

WikiText-103 is large enough to make parallel line processing visible, but small
enough for an examples folder. The default download URL points at a plain-text
zip mirror because the current Hugging Face mirror stores WikiText as Parquet.
Use `--url` to choose a different zip source.
