import Lake
open Lake DSL

package "lean-cats" where
  version := v!"0.1.0"

lean_lib «LeanCats» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-cats" where
  root := `Main

require "leanprover-community" / "mathlib"
