import Lake
open Lake DSL

require plausible from git
  "https://github.com/leanprover-community/plausible.git" @ "v4.29.0"

package lean_reducers where

extern_lib leanreducersio pkg := do
  let srcJob ← inputFile (pkg.dir / "c" / "lean_reducers_io.c") false
  let oJob ← buildO (pkg.buildDir / "c" / "lean_reducers_io.o") srcJob
    #["-I", (← getLeanInstall).includeDir.toString]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanreducersio") #[oJob]

@[default_target]
lean_lib LeanReducers where
  roots := #[`LeanReducers]
  precompileModules := true

@[default_target]
lean_exe lean_reducers_tests where
  root := `Test
  supportInterpreter := true

lean_lib ExamplesSupport where
  roots := #[`Examples.ReducerArgs]

lean_exe word_count where
  root := `Examples.WordCount
  supportInterpreter := true

lean_exe line_count where
  root := `Examples.LineCount
  supportInterpreter := true

lean_exe grep_count where
  root := `Examples.GrepCount
  supportInterpreter := true

lean_exe fetch_wikitext103 where
  root := `Examples.FetchWikiText
  supportInterpreter := true
