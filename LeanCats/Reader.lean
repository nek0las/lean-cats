import Lean
import LeanCats.Macro
import LeanCats.Syntax
import LeanCats.CatPreprocessor

open Lean.Meta Lean Expr Elab Command Parser

def evalCat (s : String) : Lean.Elab.Command.CommandElabM Unit := do
  -- parse the string using the current environment
  let env: Lean.Environment <- Lean.getEnv
  let stx?: Except String Lean.Syntax := Lean.Parser.runParserCategory env `command s "<CatFile>"
  let stx : Lean.Syntax <- Lean.ofExcept stx?

  -- We call this function to expand the macro using the Cat macro.
  let catStx <- Lean.Elab.liftMacroM (Lean.Macro.expandMacro? stx)

  match catStx with
  | some stx => {
    Lean.Elab.Command.elabCommand stx
  }
  | none => {
    pure ()
  }

-- According to lean 4 monad map: https://github.com/leanprover-community/mathlib4/wiki/Monad-map,
-- we can call IO under the CommandM.
elab "defcat" "<" filename:str ">" : command => do
    let fn := Filename.mkName filename.getString
    let path := "LeanCats/Cats/" ++ filename.getString
    let s <- IO.FS.readFile path
    let model := "[model| " ++ fn.toString ++ " " ++ (removeComments s) ++ "]"
    -- Add the declaration to the environment
    dbg_trace model
    evalCat model

section Test

defcat <"linux.bell.test">
#check Accesses.ACQUIRE
#check Accesses.MB

end Test
