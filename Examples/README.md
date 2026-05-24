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

The fetcher is Lean code that shells out to `curl` and `unzip`, and writes:

- `Examples/data/wikitext-103/train.csv`
- `Examples/data/wikitext-103/test.csv`

WikiText-103 is large enough to make parallel line processing visible, but small
enough for an examples folder. The default download URL points at a plain-text
zip mirror because the current Hugging Face mirror stores WikiText as Parquet.
Use `--url` to choose a different zip source.
