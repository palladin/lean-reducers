import Lake
open Lake DSL

package lean_reducers where

@[default_target]
lean_lib LeanReducers where
  roots := #[`LeanReducers]

@[default_target]
lean_exe lean_reducers_tests where
  root := `Test
