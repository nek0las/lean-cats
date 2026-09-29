import LeanCats.CatParser.Macro

open Lean Elab Command

namespace CatSyntax

scoped elab "defcat" "<" filename:str ">" : command => do
    let input := filename.getString
    let hasPath := input.contains '/' || input.contains '\\'
    let file := if hasPath || input.contains '.' then input else input ++ ".cat"
    let path := if hasPath then file else "LeanCats/Models/" ++ file
    let fn := Filename.mkName file
    if fn == .anonymous then
      throwError "invalid CAT model filename: {input}"
    let insts ← parseCatFile path
    let name := mkIdent fn
    elabCommand (← `([model| $name:ident $insts:inst*]))

end CatSyntax
