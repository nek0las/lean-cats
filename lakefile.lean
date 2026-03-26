import Lake
open Lake DSL

package "lean-cats" where
  version := v!"0.1.0"

lean_lib «LeanCats» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-cats" where
  root := `Main

lean_exe "litmus-parser-test" where
  root := `LeanCats.LitmusParserTest

lean_lib «LeanCatsReaderTest» where
  roots := #[`LeanCats.LitmusReaderTest]

require "leanprover-community" / "mathlib"

-- You should replace v0.0.3 with the latest version published under Releases
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.90"
