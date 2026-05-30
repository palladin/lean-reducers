# Examples

## Common Options

The reducer examples share the same parallel configuration and diagnostics
flags:

```text
--baseline              run the sequential ReducerSeq implementation
--grain N               set the smallest byte range worth splitting
--max-depth N           set reducer split depth; ranges are capped at 2^N
--diagnostics           show a colorized top-anchored diagnostics panel
--diagnostics-output D  choose console, stderr, or stdout
--help                  show help
```

## Line Count

`line_count` is a deliberately small parallel file-reducer example:

```lean
ReducerPar.readLinesFromFiles paths
  |>.reduceMapWithLawsWithConfig cfg (MonoidSpec.additive Nat) (fun _ => 1)
```

Run it on the bundled sample:

```sh
lake exe line_count Examples/sample/wiki.train.sample.txt
```

Show the diagnostics panel while counting the larger WikiText-103 file:

```sh
lake exe line_count --diagnostics Examples/data/wikitext-103/train.csv
```

Compare it with the sequential Lean baseline:

```sh
lake exe line_count --baseline Examples/data/wikitext-103/train.csv
```

Line producers follow `String.splitOn "\n"` semantics, so a trailing newline
contributes a final empty line segment.

## Grep Count

`grep_count` counts lines containing a non-empty fixed string. Its filtering and
counting steps are fused into the parallel line reducer:

```lean
ReducerPar.readLinesFromFiles paths
  |>.filter (fun line => line.contains pattern)
  |>.reduceMapWithLawsWithConfig cfg (MonoidSpec.additive Nat) (fun _ => 1)
```

Run it on the bundled sample:

```sh
lake exe grep_count reducers Examples/sample/wiki.train.sample.txt
```

Show diagnostics on the larger WikiText-103 file:

```sh
lake exe grep_count --diagnostics the Examples/data/wikitext-103/train.csv
```

Compare it with the sequential Lean baseline:

```sh
lake exe grep_count the Examples/data/wikitext-103/train.csv
lake exe grep_count --baseline the Examples/data/wikitext-103/train.csv
```

## Word Count

`word_count` is a small executable that counts normalized ASCII words across one
or more text files. It is meant to exercise the reducer path that matters for
large text workloads:

```lean
ReducerPar.readLinesFromFiles paths
  |>.flatMap wordsOfLine
  |>.groupBy (MonoidSpec.additive Nat) id (fun _ count => count + 1)
```

`wordsOfLine` returns a `ReducerSeq String`, so token emission is fused into the
outer reduction without allocating an intermediate word array.

Run the bundled smoke sample:

```sh
lake exe word_count --top 10 Examples/sample/wiki.train.sample.txt
```

For a larger demo, download and extract WikiText-103 into plain text files:

```sh
lake exe fetch_wikitext103
lake exe word_count --top 25 Examples/data/wikitext-103/train.csv
```

Run the same fused pipeline through `ReducerSeq`:

```sh
lake exe word_count --baseline --top 25 Examples/data/wikitext-103/train.csv
```

Try different reducer split depths:

```sh
lake exe word_count --max-depth 0 --top 25 Examples/data/wikitext-103/train.csv
lake exe word_count --max-depth 5 --top 25 Examples/data/wikitext-103/train.csv
lake exe word_count --max-depth 6 --top 25 Examples/data/wikitext-103/train.csv
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
auto-detected. Process memory and IO are sampled from OS process counters, while
system memory is sampled separately. Progress is still measured inside the
line-range scheduler.

The fetcher is Lean code that shells out to `curl` and `unzip`, and writes:

- `Examples/data/wikitext-103/train.csv`
- `Examples/data/wikitext-103/test.csv`

WikiText-103 is large enough to make parallel line processing visible, but small
enough for an examples folder. The default download URL points at a plain-text
zip mirror because the current Hugging Face mirror stores WikiText as Parquet.
Use `--url` to choose a different zip source.
