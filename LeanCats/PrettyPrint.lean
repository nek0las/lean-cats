import LeanCats.Data
import Mathlib.Basic.Rel
import Lean

namespace PrettyPrint

open Lean

/-- Print CAT source with one final newline, whether it is a model or an expression. -/
def printCatSource (source : String) : IO Unit :=
  IO.print (if source.endsWith "\n" then source else source ++ "\n")

/-- Print a reconstructed model (`#print_cat model`) or one of its expressions
(`#print_cat model.name`) in CAT syntax. -/
syntax "#print_cat " ident : command

/-- Write a reconstructed model to a `.cat` file. -/
syntax "#write_cat " ident str : command

macro_rules
  | `(#print_cat $name:ident) => do
    let sourceName := mkIdent (Name.str name.getId "cat")
    `(#eval PrettyPrint.printCatSource $sourceName)
  | `(#write_cat $name:ident $path:str) => do
    let sourceName := mkIdent (Name.str name.getId "cat")
    `(#eval IO.FS.writeFile $path $sourceName)

/-- Render the members of `set` which occur in `domain`. -/
def set (render : α → String) (domain : List α) (set : Set α)
    [DecidablePred set] : String :=
  "{" ++ String.intercalate ", " ((domain.filter fun value => decide (set value)).map render) ++ "}"

/-- Render the pairs of `relation` whose endpoints occur in the supplied universes. -/
def setRel (renderLeft : α → String) (renderRight : β → String)
    (leftUniverse : List α) (rightUniverse : List β) (relation : SetRel α β)
    [DecidablePred relation] : String :=
  let pairs := leftUniverse.flatMap fun left =>
    (rightUniverse.filter fun right => decide (relation (left, right))).map fun right =>
      s!"({renderLeft left}, {renderRight right})"
  "{" ++ String.intercalate ", " pairs ++ "}"

/-- Print a set after restricting it to `domain`. Useful with `#eval`. -/
def printSet (render : α → String) (domain : List α) (set : Set α)
    [DecidablePred set] : IO Unit :=
  IO.println (PrettyPrint.set render domain set)

/-- Print a relation after restricting it to the supplied endpoint universes. -/
def printSetRel (renderLeft : α → String) (renderRight : β → String)
    (leftUniverse : List α) (rightUniverse : List β) (relation : SetRel α β)
    [DecidablePred relation] : IO Unit :=
  IO.println (PrettyPrint.setRel renderLeft renderRight leftUniverse rightUniverse relation)

/-- A compact label for the project's `Data.Event` type. -/
def event (value : Data.Event) : String :=
  let operation := match value.effect.op with
    | .write => "W"
    | .read => "R"
    | .fence => "F"
    | .branch => "B"
  let storedValue := match value.effect.value with
    | some number => s!"={number}"
    | none => ""
  s!"{operation}(loc={value.effect.location}{storedValue})[id={value.id}, tid={value.t_id}]"

/-- Render a set of project events over an explicit finite event universe. -/
def eventSet (domain : List Data.Event) (set : Set Data.Event)
    [DecidablePred set] : String :=
  PrettyPrint.set event domain set

/-- Render an event relation over an explicit finite event universe. -/
def eventSetRel (domain : List Data.Event) (relation : SetRel Data.Event Data.Event)
    [DecidablePred relation] : String :=
  PrettyPrint.setRel event event domain domain relation

/-- Print a set of project events over an explicit finite event universe. -/
def printEventSet (domain : List Data.Event) (set : Set Data.Event)
    [DecidablePred set] : IO Unit :=
  IO.println (eventSet domain set)

/-- Print an event relation over an explicit finite event universe. -/
def printEventSetRel (domain : List Data.Event) (relation : SetRel Data.Event Data.Event)
    [DecidablePred relation] : IO Unit :=
  IO.println (eventSetRel domain relation)

/-!
Examples:

```lean
#print_cat tsox
-- Print the full `tsox` model in CAT syntax.

#write_cat tsox "tsox.cat"
-- Write the reconstructed model to a file.

#eval PrettyPrint.printSet toString [0, 1, 2, 3] {0, 2}
-- {0, 2}

#eval PrettyPrint.printSetRel toString toString [0, 1, 2] [0, 1, 2]
  (fun (left, right) => left < right)
-- {(0, 1), (0, 2), (1, 2)}

-- For project relations, use the candidate execution's finite event list:
#eval PrettyPrint.printEventSetRel events candidateExecution.rf'
```
-/

end PrettyPrint
