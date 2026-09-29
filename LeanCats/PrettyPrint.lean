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

private def catNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '-' || c == '.'

private def catSource? (env : Environment) (name : Name) : Option String :=
  match env.find? name with
  | some (.defnInfo info) =>
    match info.value with
    | .lit (.strVal s) => some s
    | _ => none
  | _ => none

private partial def substituteCatArg (chars : List Char) (parameter argument : String) : String :=
  match chars with
  | [] => ""
  | c :: rest =>
    if catNameChar c then
      let (tail, after) := rest.span catNameChar
      let token := String.ofList (c :: tail)
      (if token == parameter then "(" ++ argument ++ ")" else token) ++
        substituteCatArg after parameter argument
    else
      c.toString ++ substituteCatArg rest parameter argument

private partial def takeCatArg (chars : List Char) (depth : Nat := 1)
    (acc : List Char := []) : Option (String × List Char) :=
  match chars with
  | [] => none
  | c :: rest =>
    if c == '(' then
      takeCatArg rest (depth + 1) (c :: acc)
    else if c == ')' then
      if depth == 1 then some (String.ofList acc.reverse, rest)
      else takeCatArg rest (depth - 1) (c :: acc)
    else
      takeCatArg rest depth (c :: acc)

private def catBody (source : String) : String :=
  let source := source.trimAscii.toString
  if source.startsWith "try " then
    ((source.drop 4).toString.splitOn " with ").head!
  else source

private def catWrapped (source : String) : Bool :=
  let rec check (chars : List Char) (depth : Nat) : Bool :=
    match chars with
    | [] => depth == 0
    | '(' :: rest => check rest (depth + 1)
    | ')' :: rest =>
      if depth == 1 then rest.isEmpty
      else if depth == 0 then false
      else check rest (depth - 1)
    | _ :: rest => check rest depth
  match source.trimAscii.toString.toList with
  | '(' :: rest => check rest 1
  | _ => false

private def catParenthesize (source : String) : String :=
  if catWrapped source then source else "(" ++ source ++ ")"

private partial def expandCatFormula (env : Environment) (ns : Name)
    (visited : List Name) (chars : List Char) : Lean.Elab.Command.CommandElabM String := do
  match chars with
  | [] => return ""
  | c :: rest =>
    if !catNameChar c then
      return c.toString ++ (← expandCatFormula env ns visited rest)
    let (tail, after) := rest.span catNameChar
    let token := String.ofList (c :: tail)
    let decl := Name.str ns (token.replace "-" "_")
    let some source := catSource? env (Name.str decl "cat")
      | return token ++ (← expandCatFormula env ns visited after)
    if visited.contains decl then
      throwError "cyclic CAT definition while expanding {decl}"
    let body := catBody source
    let some parameter := catSource? env (Name.str decl "catArg")
      | return catParenthesize (← expandCatFormula env ns (decl :: visited) body.toList) ++
          (← expandCatFormula env ns visited after)
    let (_, call) := after.span Char.isWhitespace
    match call with
    | '(' :: callRest =>
      let some (argument, remaining) := takeCatArg callRest
        | throwError "unclosed CAT function call: {token}"
      let substituted := substituteCatArg body.toList parameter argument
      return catParenthesize (← expandCatFormula env ns (decl :: visited) substituted.toList) ++
        (← expandCatFormula env ns visited remaining)
    | _ => return token ++ (← expandCatFormula env ns visited after)

/-- Print a CAT formula with locally defined aliases recursively expanded. -/
elab "#print_cat_expanded " name:ident : command => do
  let decl := name.getId
  let env ← Lean.getEnv
  let some source := catSource? env (Name.str decl "cat")
    | throwError "no CAT formula stored for {decl}"
  let expanded ← expandCatFormula env decl.getPrefix [decl] (catBody source).toList
  Lean.logInfo m!"{decl} = {expanded}"

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

#print_cat_expanded mips.pso
-- Expand CAT definitions used by `mips.pso`, stopping at built-in relations.

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
