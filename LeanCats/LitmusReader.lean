/-
  LitmusReader.lean — Read litmus test files from disk and enumerate candidate executions.

  Usage (inside a Lean file):

  ```
  -- Read a litmus file, parse it, enumerate candidate executions, and print results.
  #litmus "examples/tests/SB.litmus"

  -- Read and bind the candidate executions to a definition.
  deflitmus sb_execs < "examples/tests/SB.litmus" >
  #eval sb_execs.size
  ```
-/
import Lean
import LeanCats.LitmusParser

open Lean Elab Command Meta
open LitmusParser LitmusParser.X86

/-- Read a litmus file from disk (relative to the workspace root). -/
private def readLitmusFile (path : String) : IO String :=
  IO.FS.readFile path

/-- Parse and enumerate candidate executions from a litmus file string. -/
private def processLitmus (contents : String) : Except String (Array ConcreteCandExec) :=
  X86.parseLitmusAndEnumerate contents

/-- Format candidate executions for display. -/
private def formatResults (label : String) (execs : Array ConcreteCandExec) : String :=
  let header := s!"{label}: {execs.size} candidate execution(s)\n"
  execs.foldl (fun acc r => acc ++ s!"---\n{r}\n") header

/-- `#litmus "path/to/test.litmus"` — read, parse, enumerate, and print results. -/
elab "#litmus" path:str : command => do
  let filePath := path.getString
  let contents ← IO.FS.readFile filePath
  match processLitmus contents with
  | .ok execs =>
    let label := filePath.splitOn "/" |>.getLast!
    logInfo (formatResults label execs)
  | .error e =>
    throwError s!"Litmus parse error: {e}"

/-- `deflitmus name < "path/to/test.litmus" >` — read a litmus file and define
    `name : Array ConcreteCandExec` in the environment. -/
elab "deflitmus" name:ident "<" path:str ">" : command => do
  let filePath := path.getString
  let contents ← IO.FS.readFile filePath
  match processLitmus contents with
  | .ok execs =>
    -- Build the term by first turning the execution array into source text,
    -- then storing the raw string + reparsing at use-site via a thunk.
    -- For simplicity, we define it as an opaque constant backed by native_decide / IO.
    -- The simplest approach: store the file content and re-parse at #eval time.
    let contentLit := Lean.Syntax.mkStrLit contents
    let cmd ← `(
      def $(name) : Array LitmusParser.ConcreteCandExec :=
        match LitmusParser.X86.parseLitmusAndEnumerate $contentLit with
        | .ok execs => execs
        | .error _ => #[]
    )
    elabCommand cmd
    logInfo s!"Defined '{name.getId}' with {execs.size} candidate execution(s)"
  | .error e =>
    throwError s!"Litmus parse error ({filePath}): {e}"
