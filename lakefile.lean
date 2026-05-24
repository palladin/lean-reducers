import Lake
open Lake DSL

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
