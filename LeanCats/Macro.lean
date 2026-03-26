import LeanCats.Syntax
import Lean
import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic
import Std.Data.HashMap
import LeanCats.HashMapExt

open Lean Elab Command Term Meta
open Data

syntax "[model|" ident inst* "]" : command
syntax (name := catexpr) "[expr|" expr "," cat_ident "," cat_ident "," cat_ident "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term
syntax (name := catinst) "[inst|" inst "," cat_ident "," cat_ident "," cat_ident "]" : command
syntax "[annotable-events|" annotable_events "," cat_ident "," cat_ident "]" : term -- Set
syntax "[predefined-events|" predefined_events "," cat_ident "," cat_ident "]" : term
syntax "[reserved|" reserved "," cat_ident "," cat_ident "]" : term
syntax "[predefined-relations|" predefined_relations "," cat_ident "," cat_ident "]" : term
syntax "[dsl-term|" dsl_term "," cat_ident "," cat_ident "," cat_ident "]" : term

-- Walk any cat_ident syntax tree, collect all ident leaves, and join with "_".
-- This handles plain idents, tick-prefixed ('ONCE), and multi-hyphen (rcu-lock, after-unlock-lock).
partial def catIdentToName (stx : Syntax) : Name :=
  let rec go (s : Syntax) : Array String :=
    if s.isIdent then #[s.getId.toString]
    else if s.isAtom then #[]  -- skip punctuation atoms like "'" and "-"
    else s.getArgs.foldl (fun acc a => acc ++ go a) #[]
  let parts := go stx
  match parts with
  | #[] => `_unknown
  | _   =>
    let joined := parts[1:].foldl (fun acc s => acc ++ "_" ++ s) parts[0]!
    joined.toName

instance : Coe (TSyntax `cat_ident) (TSyntax `ident) where
  coe s := mkIdent (catIdentToName s.raw)

instance : Coe (TSyntax `ident) (TSyntax `cat_ident) where
  coe s := mkNode `cat_ident #[s]

instance : Coe (TSyntax `ident) (TSyntax `annotable_events) where
  coe s := mkNode `annotable_events #[s]

instance : Coe (TSyntax `predefined_events) (TSyntax `expr) where
  coe s := mkNode `expr #[s]

instance : Coe (TSyntax `predefined_relations) (TSyntax `expr) where
  coe s := mkNode `expr #[s]

-- Set α -> Set (α × α)
def SetRel.mkId (s : Set Event) : SetRel Event Event :=
  fun (e₁, e₂) => e₁ = e₂ ∧ e₁ ∈ s

macro_rules
  | `([dsl-term| $i:cat_ident, $evts, $X, $arg]) =>
    -- Apply the arg instead of using the id in the env.
    if arg.getId = i.getId then
      `($i)
    else
      `($i $evts $X)

macro_rules
  | `([expr| $e₁:expr | $e₂:expr, $evts, $X, $arg]) =>
    `(CatRel.CatUnion.union ([expr| $e₁, $evts, $X, $arg]) ([expr| $e₂, $evts, $X, $arg]))

  | `([expr| $e₁:expr & $e₂:expr, $evts, $X, $arg]) =>
    `(Set.inter ([expr| $e₁, $evts, $X, $arg]) ([expr| $e₂, $evts, $X, $arg]))

  | `([expr| $e₁:expr ; $e₂:expr, $evts, $X, $arg]) =>
    `(SetRel.comp ([expr| $e₁, $evts, $X, $arg]) ([expr| $e₂, $evts, $X, $arg]))

  | `([expr| [ $i:expr ], $evts, $X, $arg]) =>
    `(SetRel.mkId ([expr| $i, $evts, $X, $arg]))

  | `([expr| $e₁:expr * $e₂:expr, $evts, $X, $arg]) =>
    `(CatRel.prod ([expr| $e₁, $evts, $X, $arg]) ([expr| $e₂, $evts, $X, $arg]))

  | `([expr| ~ $e:expr, $evts, $X, $arg]) =>
    `(Set.compl ([expr| $e, $evts, $X, $arg]))

  | `([expr| $e₁:expr \ $e₂:expr, $evts, $X, $arg]) =>
    `(Set.diff ([expr| $e₁, $evts, $X, $arg]) ([expr| $e₂, $evts, $X, $arg]))

  | `([expr| $e^-1, $evts, $X, $arg]) =>
    `(Rel.inv ([expr| $e, $evts, $X, $arg]))

  | `([expr| $e ?, $evts, $X, $arg]) =>
    `(([expr| $e, $evts, $X, $arg]) ∪ {(e₁, e₂) | e₁ = e₂})

  | `([expr| $e *, $evts, $X, $arg]) =>
    `(([expr| $e, $evts, $X, $arg]) ∪ {(e₁, e₂) | e₁ = e₂})

  | `([expr| $e +, $evts, $X, $arg]) =>
    `(([expr| $e, $evts, $X, $arg]))

  | `([expr| $r:reserved, $evts, $X, $_]) =>
    `([reserved| $r, $evts, $X])

  | `([expr| ($e:expr), $evts, $X, $arg]) =>
    `([expr| $e, $evts, $X, $arg])

  | `([expr| $t:dsl_term, $evts, $X, $arg]) =>
    `(([dsl-term| $t, $evts, $X, $arg]))

  | `([expr| $i:dsl_term ($e:expr), $evts, $X, $arg]) => do
    -- function call.
    `(([dsl-term| $i, $evts, $X, $arg]) ([expr| $e, $evts, $X, $arg]))

macro_rules
  | `([reserved| $r:predefined_relations, $evts, $X]) =>
    `([predefined-relations| $r, $evts, $X])
  | `([reserved| $e:predefined_events, $evts, $X]) => `([predefined-events| $e, $evts, $X])

macro_rules
  | `([predefined-relations| fr, $_, $X]) =>
    let nm := mkIdent "fr".toName
    `($X.$nm)

  | `([predefined-relations| po, $_, $X]) =>
    let nm := mkIdent "po".toName
    `($X.$nm)

  | `([predefined-relations| rf, $_, $X]) =>
    let nm := mkIdent "rf".toName
    `($X.$nm)

  | `([predefined-relations| rmw, $_, $X]) =>
    let nm := mkIdent "rmw".toName
    `($X.$nm)

  | `([predefined-relations| co, $_, $X]) =>
    let co' := mkIdent "co".toName
    `($X.$co')

  | `([predefined-relations| id, $_, $_]) =>
    `(SetRel.id)

  | `([predefined-relations| data, $_, $X]) =>
    let nm := mkIdent "data".toName
    `($X.$nm)

  | `([predefined-relations| addr, $_, $X]) =>
    let nm := mkIdent "addr".toName
    `($X.$nm)

  | `([predefined-relations| ctrl, $_, $X]) =>
    let nm := mkIdent "ctrl".toName
    `($X.$nm)

  | `([predefined-relations| wmb, $_, $X]) =>
    let nm := mkIdent "wmb".toName
    `($X.$nm)

  | `([predefined-relations| fence, $_, $X]) =>
    let nm := mkIdent "fence".toName
    `($X.$nm)

  | `([predefined-relations| rmb , $_, $X]) =>
    let nm := mkIdent "rmb".toName
    `($X.$nm)

  | `([predefined-relations| mb , $_, $X]) =>
    let nm := mkIdent "mb".toName
    `($X.$nm)

macro_rules
  | `([keyword| and]) => Lean.Macro.throwUnsupported
  | `([keyword| as]) => Lean.Macro.throwUnsupported
  | `([keyword| begin]) => Lean.Macro.throwUnsupported
  | `([keyword| call]) => Lean.Macro.throwUnsupported
  | `([keyword| do]) => Lean.Macro.throwUnsupported
  | `([keyword| end]) => Lean.Macro.throwUnsupported
  | `([keyword| enum]) => Lean.Macro.throwUnsupported
  | `([keyword| flag]) => Lean.Macro.throwUnsupported
  | `([keyword| forall]) => Lean.Macro.throwUnsupported
  | `([keyword| from]) => Lean.Macro.throwUnsupported
  | `([keyword| fun]) => Lean.Macro.throwUnsupported
  | `([keyword| in]) => Lean.Macro.throwUnsupported
  | `([keyword| let]) => Lean.Macro.throwUnsupported
  | `([keyword| match]) => Lean.Macro.throwUnsupported
  | `([keyword| procedure]) => Lean.Macro.throwUnsupported
  | `([keyword| rec]) => Lean.Macro.throwUnsupported
  | `([keyword| scopes]) => Lean.Macro.throwUnsupported
  | `([keyword| with]) => Lean.Macro.throwUnsupported
  | `([keyword| $a:assertion]) => `([assertion| $a])

macro_rules
  | `([assertion| irreflexive]) => `(CatRel.SetRel.Irreflexive)
  | `([assertion| acyclic]) => `(CatRel.SetRel.Acyclic)
  | `([assertion| empty]) => `(CatRel.SetRel.IsEmpty)

macro_rules
  | `([annotable-events| W, $evts, $X]) =>
    let nm := mkIdent "W".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| R, $evts, $X]) =>
    let nm := mkIdent "R".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| B, $evts, $X]) =>
    let nm := mkIdent "B".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| F, $evts, $X]) =>
    let nm := mkIdent "F".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| RMW, $evts, $X]) =>
    let nm := mkIdent "RMW".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| SRCU, $evts, $X]) =>
    let nm := mkIdent "SRCU".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| M, $evts, $X]) =>
    let nm := mkIdent "M".toName
    `(($X.$evts.$nm : Set Event))

macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW, $evts, $_]) =>
    let nm := mkIdent "IW".toName
    `($evts.$nm)

  | `([predefined-events| M, $evts, $_]) =>
    let nm := mkIdent "M".toName
    `($evts.$nm)

  | `([predefined-events| $a:annotable_events, $evts, $X]) =>
    `([annotable-events| $a, $evts, $X])

macro_rules
  -- We just ignore the include inst.
  | `([inst| include $_filename:str , $_ , $_, $_]) => return mkNullNode

  | `([inst| let $nm:cat_ident = $e, $evts, $X, $arg]) =>
    `(@[simp] def $nm := [expr|$e, $evts, $X, $arg])

  | `([inst| let $nm:cat_ident ( $arg:cat_ident ) = $e:expr, $evts, $X, $_]) => do
    -- This is where we use the real arg.
    `(@[simp] def $nm ($arg:ident : SetRel Event Event) := [expr| $e, $evts, $X, $arg])

  | `([inst| $a:assertion $e as $nm:cat_ident, $evts, $X, $arg]) => do
    `(@[simp] def $nm := ([assertion| $a] ([expr| $e, $evts, $X, $arg])))

  | `([inst| ~$a:assertion $e as $nm:cat_ident, $evts, $X, $arg]) => do
    `(@[simp] def $nm := [assertion| $a] (¬[expr| $e, $evts, $X, $arg]))

  | `([inst| enum $nm:cat_ident = $[ $tags:cat_ident ]||*, $_, $_, $_]) => do
    let nmIdent : TSyntax `ident := nm
    -- Convert each cat_ident tag to a plain Lean ident (handles multi-hyphen names like rcu-lock → rcu_lock, and adds trailing ').
    let tagIdents : Array (TSyntax `ident) := tags.map (fun t =>
      mkIdent (Name.mkSimple ((catIdentToName t.raw).toString)))
    let indef <- `(
      inductive $nmIdent where $[| $tagIdents:ident ]*
    )
    -- Create unqualified aliases, e.g. `ONCE` → `Accesses.ONCE`.
    let aliases <- tagIdents.mapM fun (tagId : TSyntax `ident) => do
      let qualName := mkIdent (nmIdent.getId ++ tagId.getId)
      `(def $tagId := $qualName)
    let ret := #[indef] ++ aliases
    return mkNullNode ret

  | `([inst| flag $_:assertion $_:expr as $_:expr, $_, $_, $_]) => do
    -- We ignore the flag for now, since it doesn't change the states of the execution, it's just used to witness the assertion.
    return mkNullNode #[]

/--
Processes `instructions A[EnumType]` by generating a definition for each constructor of `EnumType`.
Specifically, for each constructor `C` of `EnumType`, we generate:
  `def C : Set Event := { e | e.tag = EnumType.C } ∩ A`

For example, given `enum Accesses = ONCE || RELEASE || ...` and `instructions R[Accesses]`,
we generate:
  `def ONCE : Set Event := { e | e.tag = Accesses.ONCE } ∩ R`
  `def RELEASE : Set Event := { e | e.tag = Accesses.RELEASE } ∩ R`
  ...
-/
@[command_elab catinst]
def elabCatInst : CommandElab := fun stx => do
  match stx with
  | `([inst| instructions { $a:annotable_events,* }[ $c:cat_ident ] , $evts:cat_ident , $X:cat_ident, $_:cat_ident]) => do
    let currNamespace <- getCurrNamespace
    -- This is used to get the full name with namespace.
    let typeName := Name.updatePrefix c.getId currNamespace

    let info <- getConstInfoInduct typeName

    let commands <- info.ctors.mapM (
      fun ctor => do
        -- Make the constructors name correct by removing the end tick.
        let ctorName : Name := ctor.lastComponentAsString.dropEnd 1 |>.toName |>.capitalize
        -- TODO(Nekolas): Make this part `∩ [annotable-events| $a]` work.
        if (<-getEnv).contains ctorName then
          return (TSyntax.mk $ mkNullNode #[])
        else
          let ctorDef <- `({e | e.tag = ⟨$(mkIdent typeName), $(mkIdent ctor)⟩ })

          let inters : TSyntax `term ← a.getElems.foldlM
            (fun (acc : TSyntax `term) (ae_i : TSyntax `annotable_events) => do
            `( $acc ∩ [annotable-events| $ae_i, $evts, $X] )) ctorDef

          let ctorDef <- `(
            abbrev $(mkIdent ctorName) :
              Set Event := $inters
          )
          return ctorDef
        )
    -- A hack to return the commands, the mkNullNode create a SyntaxTree and we use the elabCommand to execute it.
    elabCommand $ mkNullNode commands.toArray
  | _ => Lean.Elab.throwUnsupportedSyntax

macro_rules
  -- Create the model.
  | `([model| $n:ident $xs:inst*]) => do
    let nstart <- `(namespace $n)
    let placeHolder := mkIdent `__
    let evts := mkIdent `evts
    let X := mkIdent `x
    let vars <- `(variable ($evts : Events) [IsStrictTotalOrder Event (CatRel.preCo $evts)] ($X : CandidateExecution $evts))
    let nend <- `(end $n)
    let insts <- xs.mapM (fun ins => `([inst| $ins, $evts, $X, $placeHolder]))

    -- let insts : Array (TSyntax `command) := #[]
    let ret := #[nstart] ++ #[vars] ++ insts ++ #[nend]
    return mkNullNode ret

@[simp] def domain (evts : Events) (_ : CandidateExecution evts) (r : SetRel Event Event) := SetRel.dom r

@[simp] def range (evts : Events) (_ : CandidateExecution evts) (r : SetRel Event Event) := SetRel.cod r

@[simp] def po_loc (evts : Events) (X : CandidateExecution evts) := X.po' ∩ CatRel.Rel.location

@[simp] def fre (evts : Events) (X : CandidateExecution evts) := X.fr ∩ CatRel.Rel.external

@[simp] def rfe (evts : Events) (X : CandidateExecution evts) := X.rf' ∩ CatRel.Rel.external

@[simp] def rfi (evts : Events) (X : CandidateExecution evts) := X.rf' ∩ CatRel.Rel.internal

@[simp] def coe (evts : Events) (X : CandidateExecution evts) := X.co' ∩ CatRel.Rel.external

@[simp] def int (evts : Events) (_ : CandidateExecution evts) := CatRel.Rel.internal

@[simp] def ext (evts : Events) (_ : CandidateExecution evts) := CatRel.Rel.external

[model| lkmm

enum Accesses = ONCE' ||
  RELEASE'  ||
  ACQUIRE'  ||
  NORETURN'  ||
  MB'
instructions {R, W, RMW}[Accesses]

enum Barriers = wmb'  ||
  rmb'  ||
  barrier'

instructions {F}[Barriers]

let FailedRMW = RMW \ (domain(rmw) | range(rmw))
let Acquire = ACQUIRE \ W \ FailedRMW
let Release = RELEASE \ R \ FailedRMW
let Mb = MB \ FailedRMW
let Noreturn = NORETURN \ W

let Marked = (~M) | IW | ONCE | RELEASE | ACQUIRE | MB | RMW

let Plain = M \ Marked

let strong_fence = mb

-- Acquire-Release
let acq_po = [Acquire] ; po ; [M]
let po_rel = [M] ; po ; [Release]

-- SCPV
let com = rf | co | fr
acyclic po_loc | com as coherence

-- Atomic Read-Modify-Write
empty rmw & (fre ; coe) as atomic

-- Preserved Program Order
let dep = addr | data
let rwdep = (dep | ctrl) ; [W]
let overwrite = co | fr
let to_w = rwdep | (overwrite & int) | (addr ; [Plain] ; wmb)
let to_r = addr | (dep ; [Marked] ; rfi)
let ppo = to_r | to_w | fence

let A_cumul(r) = (rfe ; [Marked])? ; r

let a = A_cumul(po_rel)

let cumul_fence = [Marked] ; (A_cumul(strong_fence | po_rel) | wmb) ; [Marked]
let prop = [Marked] ; (overwrite & ext)? ; cumul_fence* ; [Marked] ; (rfe)? ; [Marked]

-- Happends Before Relation
let hb = [Marked] ; (ppo | rfe | ((prop \ id) & int)) ; [Marked]

acyclic hb as happens_before

-- Propagation Before Relation
let pb = prop ; strong_fence ; hb* ; [Marked]
acyclic pb as propagation
]

#reduce lkmm.ACQUIRE
#reduce lkmm.coherence
#reduce lkmm.atomic
#reduce lkmm.happens_before
#reduce lkmm.propagation

[model| tso_x86

let xppo = ((W*W) | (R*W) | (R*R)) & po
let At = domain(rmw) | range(rmw)
let implied = po;[At | F] | [At | F];po
acyclic (implied | xppo | rfe | fr | co) as tso
]
