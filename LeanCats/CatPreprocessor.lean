
import Std.Data.HashMap

namespace String
@[specialize]
def foldl2Aux {α : Type u} (f : α → Char → Char → α) (s : String) (stopPos : Pos.Raw) (i : Pos.Raw) (a : α) : α :=
  if h : i.byteIdx < stopPos.byteIdx then
    have := Nat.sub_lt_sub_left h (String.Pos.Raw.byteIdx_lt_byteIdx_next s i)
    let nextIdx := Pos.Raw.next s i
    match Pos.Raw.get? s nextIdx with
      | none => a
      | some next =>
        foldl2Aux f s stopPos nextIdx (f a (Pos.Raw.get s i) next)
  else a
termination_by stopPos.byteIdx - i.byteIdx

@[inline] def foldl2 {α : Type u} (f : α → Char → Char → α) (init : α) (s : String) : α :=
  foldl2Aux f s s.endPos.1 ⟨0⟩ init
end String

inductive InComment
  | entering
  | inside
  | leaving
  | outside
deriving Inhabited

@[inline]
private def processBlock (accIncomment : String × InComment)  : Char → Char → String × InComment :=
  let ⟨acc, inComment⟩ := accIncomment
  fun c₁ c₂ => match c₁,c₂ with
  | '(', '*' => match inComment with
    | .outside => (acc, .entering)
    | .entering => panic! s!"Error (entering block, first) when removing comments at {acc}."
    | .leaving => panic! s!"Error (leaving block, first) when removing comments at {acc}."
    | .inside => (acc, .inside)
  | c@'*', ')' => match inComment with
    | .inside => (acc, .leaving)
    | .entering => (acc, .inside)
    | .leaving => panic! s!"Error (leaving block, second) when removing comments at {acc}."
    | .outside => (acc.push c, .outside)
  | c, _ => match inComment with
    | .inside => (acc, .inside)
    | .outside => (acc.push c, .outside)
    | .entering => match c with
      | '*' => (acc, .inside)
      | _ => panic! s!"Error (entering block) when removing comments at {acc}"
    | .leaving => match c with
      | ')' => (acc, .outside)
      | _ => panic! s!"Error (leaving block) when removing comments at {acc}"

def removeBlockComments (input : String) : String :=
  -- add a `\n` in the end that should be ignored by size-2 window
  (input.push '\n').foldl2 processBlock (String.ofList [], .outside) |>.1

private def processHead (accDone : String × Bool)  : Char → String × Bool :=
  let ⟨acc, done⟩ := accDone
  fun c => if done then (acc.push c, true) else
    match c with
    | '"' => (acc, true)
    | _ => (acc, false)

def removeFrontTick (input : String) : String :=
  (input.splitOn.map (fun s => s.stripPrefix "\'")) |> (String.intercalate " ")
  |>.splitOn "\n" |>.map (fun s => s.stripPrefix "\'") |> (String.intercalate "\n")
  |>.splitOn "\t" |>.map (fun s => s.stripPrefix "\'") |> (String.intercalate " ")

def removeTickAndCapitalize (s : String) : String :=
  let stripped := (s.dropPrefix "\'").toString
  if stripped.isEmpty then
    stripped
  else
    let firstChar := String.Pos.Raw.get stripped ⟨0⟩
    let rest := stripped.drop 1
    (firstChar.toUpper.toString ++ rest)

private structure InstrGroup where
  firstIdx : Nat
  events   : Array String

private def parseInstructionsLine? (line : String) : Option (Array String × String) :=
  let trimmed := (String.trimAscii line).toString
  if !(trimmed.startsWith "instructions ") then
    none
  else
    let rest := (String.dropPrefix trimmed "instructions ").toString
    match rest.splitOn "[" with
    | [evtsRaw, tagsAndTail] =>
      match tagsAndTail.splitOn "]" with
      | [] => none
      | tag::_ =>
        let eventText := (String.trimAscii evtsRaw).toString
        let events :=
          if eventText.startsWith "{" && eventText.endsWith "}" then
            let body := ((eventText.drop 1).dropEnd 1).toString
            (body.splitOn ",").map (fun s => (String.trimAscii s).toString) |>.toArray
          else
            #[eventText]
        let tagTrimmed := (String.trimAscii tag).toString
        if events.isEmpty || tagTrimmed.isEmpty then none
        else some (events, tagTrimmed)
    | _ => none

private def mergeInstructionTagLines (input : String) : String := Id.run do
  let lines := input.splitOn "\n"
  let mut groups : Std.HashMap String InstrGroup := {}

  for i in [:lines.length] do
    let line := lines[i]!
    match parseInstructionsLine? line with
    | none => pure ()
    | some (events, tag) =>
      match groups.get? tag with
      | none =>
        groups := groups.insert tag { firstIdx := i, events := events }
      | some g =>
        let merged := events.foldl (fun acc e => if acc.contains e then acc else acc.push e) g.events
        groups := groups.insert tag { g with events := merged }

  let mut out : List String := []
  for i in [:lines.length] do
    let line := lines[i]!
    match parseInstructionsLine? line with
    | none => out := line :: out
    | some (_, tag) =>
      match groups.get? tag with
      | some g =>
        if g.firstIdx == i then
          let mergedEvts := String.intercalate ", " g.events.toList
          out := ("instructions {" ++ mergedEvts ++ "}[" ++ tag ++ "]") :: out
      | none => out := line :: out

  String.intercalate "\n" out.reverse

def removeComments (input : String) : String :=
  let removedTick := removeFrontTick input
  let headProcessed : String := match removedTick.toList with
    | [] => .ofList []
    | '"'::rest => (String.ofList rest).foldl processHead (String.ofList [], false) |>.1
    | s => .ofList s
  mergeInstructionTagLines (removeBlockComments headProcessed)

#eval removeFrontTick "'example || 'string"

#eval removeTickAndCapitalize "'once"
#eval removeTickAndCapitalize "'release"
#eval removeTickAndCapitalize "'ACQUIRE"

#eval removeComments "(**)"
#eval removeComments "(*)"
#eval removeComments "some(*)stuff"
#eval removeComments "some(**) stuff"
#eval removeComments "some(* stuff*) here"
#eval removeComments "some(*) stuff*) here"
#eval removeComments "(****)"
#eval removeComments "*)(****)(**)*("
#eval removeComments "this is a line \n(* \n a multi-line comment \n *)\n and then some "
#eval removeComments "\"a header\" with a(*n inline*) comment"

def Filename.mkName (inp : String) : Lean.Name := Id.run do
  let mut nm : List Char := []
  for c in inp.toList do
    if c.isAlpha then
      nm := c :: nm
    else if c == '.' then
      return (.str  .anonymous (String.ofList nm.reverse))
    else
      continue
  return (.str  .anonymous (String.ofList nm.reverse))

#eval Filename.mkName "foo_bar3.baz"


def enums_test := "enum Accesses = 'ONCE (*READ_ONCE,WRITE_ONCE*) ||
		'RELEASE (*smp_store_release*) ||
		'ACQUIRE (*smp_load_acquire*) ||
		'NORETURN (* R of non-return RMW *) ||
		'MB (*xchg(),cmpxchg(),...*)"

#eval removeComments enums_test

def instructions_test := "instructions R[Accesses]\ninstructions W[Accesses]\ninstructions RMW[Accesses]\ninstructions F[Barriers]"

#eval removeComments instructions_test
