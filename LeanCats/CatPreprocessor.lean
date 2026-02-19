
namespace String
@[specialize]
def foldl2Aux {α : Type u} (f : α → Char → Char → α) (s : String) (stopPos : Pos) (i : Pos) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (String.lt_next s i)
    let nextIdx := s.next i
    match s.get? nextIdx with
      | none => a
      | some next =>
        foldl2Aux f s stopPos nextIdx (f a (s.get i) next)
  else a
termination_by stopPos.1 - i.1

@[inline] def foldl2 {α : Type u} (f : α → Char → Char → α) (init : α) (s : String) : α :=
  foldl2Aux f s s.endPos 0 init
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
  (input.push '\n').foldl2 processBlock ({data := []}, .outside) |>.1

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

def removeComments (input : String) : String :=
  let removedTick := removeFrontTick input
  let headProcessed : String := match removedTick.data with
    | [] => .mk []
    | '"'::rest => (String.mk rest).foldl processHead (String.mk [], false) |>.1
    | s => .mk s
  removeBlockComments headProcessed

#eval removeFrontTick "'example || 'string"

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
  for c in inp.data do
    if c.isAlpha then
      nm := c :: nm
    else if c == '.' then
      return (.str  .anonymous {data := nm.reverse})
    else
      continue
  return (.str  .anonymous {data := nm.reverse})

#eval Filename.mkName "foo_bar3.baz"


def enums_test := "enum Accesses = 'ONCE (*READ_ONCE,WRITE_ONCE*) ||
		'RELEASE (*smp_store_release*) ||
		'ACQUIRE (*smp_load_acquire*) ||
		'NORETURN (* R of non-return RMW *) ||
		'MB (*xchg(),cmpxchg(),...*)"

#eval removeComments enums_test
