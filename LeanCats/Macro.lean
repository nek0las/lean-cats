import LeanCats.Syntax
import Lean
import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic

open Lean Elab Command Term Meta
open Data

syntax "[model|" ident inst* "]" : command
syntax "[expr|" expr "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term

syntax "[inst|" inst "]" : command
syntax "[annotable-events|" annotable_events "]" : term -- Set
syntax "[predefined-events|" predefined_events "]" : term
syntax "[reserved|" reserved "]" : term
syntax "[predefined-relations|" predefined_relations "]" : term
syntax "[dsl-term|" dsl_term "]" : term

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

macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.union ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr & $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.inter ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr ; $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      Rel.comp ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr * $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.prod ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e^-1]) =>
    `(fun X : CandidateExecution => Rel.inv ([expr| $e] X))

  | `([expr| $r:reserved]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [reserved| $r] evts X)

  | `([expr| ($e:expr)]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [expr| $e] evts X)

  | `([expr| $t:dsl_term]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [dsl-term| $t] evts X)

macro_rules
  | `([dsl-term| $i:cat_ident]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      $i evts X)

macro_rules
  | `([reserved| $r:predefined_relations]) => `([predefined-relations| $r])
  | `([reserved| $e:predefined_events]) => `([predefined-events| $e])

macro_rules
  | `([predefined-relations| fr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._fr)

  | `([predefined-relations| po]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._po)

  | `([predefined-relations| rf]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._rf)

  | `([predefined-relations| rfe]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.external X.evts X._rf)

  | `([predefined-relations| co]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.co.wellformed evts)

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
  | `([assertion| irreflexive]) => `(CatRel.Irreflexive)
  | `([assertion| acyclic]) => `(CatRel.Acyclic)
  | `([assertion| empty]) => `(CatRel.IsEmpty)

macro_rules
  | `([annotable-events| W]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.W)
  | `([annotable-events| R]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.R)
  | `([annotable-events| B]) => `(fun X : CandidateExecution => X.evts.B)
  | `([annotable-events| F]) => `(fun X : CandidateExecution => X.evts.F)
  | `([annotable-events| RMW]) => `(fun X : CandidateExecution => X.evts.RMW)

macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.IW)

  | `([predefined-events| M]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.W ∪ X.evts.R)

  | `([predefined-events| $a:annotable_events]) => `([annotable-events| $a])

macro_rules
  -- We just ignore the include inst.
  | `([inst| include $_filename:str]) => return mkNullNode

  -- TODO(Don't know how the coe works here, maybe ask others? Like the coe works, okay, but how do I know it's value?)
  | `([inst| let $nm:cat_ident = $e]) =>
    `(@[simp] def $nm := [expr|$e])

  | `([inst| $a:assertion $e as $nm:cat_ident]) => do
    `(@[simp] def $nm (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) : Prop
      := [assertion| $a] ([expr| $e] evts X))

  | `([inst| ~$a:assertion $e as $nm:cat_ident]) => do
    `(@[simp] def $nm (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) : Prop
      := ¬[assertion| $a] ([expr| $e] evts X))

  | `([inst| enum $nm:cat_ident = $[ $tags:cat_ident ]||*]) => do
    let nmIdent : TSyntax `ident := nm
    -- Convert each cat_ident tag to a plain Lean ident (handles multi-hyphen names like rcu-lock → rcu_lock).
    let tagIdents : Array (TSyntax `ident) := tags.map (fun t => mkIdent (catIdentToName t.raw))
    let indef <- `(
      inductive $nmIdent where $[| $tagIdents:ident ]*
    )
    -- Derive DecidableEq so we can state and decide `e.tag = Accesses.ONCE` in proofs.
    let decEq <- `(deriving instance DecidableEq for $nmIdent)
    -- Register as a Tag type so the vm knows this is used for event tagging.
    let tagName := mkIdent `Data.Tag
    let tagInst <- `(instance : $tagName $nmIdent where)
    -- Create unqualified aliases, e.g. `ONCE` → `Accesses.ONCE`.
    let aliases <- tagIdents.mapM fun (tagId : TSyntax `ident) => do
      let qualName := mkIdent (nmIdent.getId ++ tagId.getId)
      `(def $tagId := $qualName)
    let ret := #[indef, decEq, tagInst] ++ aliases
    return mkNullNode ret

  | `([inst| flag $_:assertion $_:expr as $_:expr]) => do
    -- We ignore the flag for now, since it doesn't change the states of the execution, it's just used to witness the assertion.
    return mkNullNode #[]

  | `([inst| instructions $_a:annotable_events [ $_c:cat_ident ]]) => do
    -- TODO(Nikolas): Add instructions support for this.
    -- By now the instructions are ignored because we don't make sure the semantics of the instrutions.
    return mkNullNode #[]

macro_rules
  -- Create the model.
  | `([model| $n:ident $x:inst*]) => do
    let nstart <- `(namespace $n)
    let nend <- `(end $n)
    let insts <- x.mapM (fun ins => `([inst| $ins]))

    -- let insts : Array (TSyntax `command) := #[]
    let ret := #[nstart] ++ insts ++ #[nend]
    return mkNullNode ret

-- Linux-kernel memory consistency model  ("linux.bell" excerpt)
-- Comments (*...*) and tick-prefixes (') are stripped by the preprocessor
-- before these lines reach the Lean syntax; we write the cleaned form here.
[inst| enum Accesses = ONCE || RELEASE || ACQUIRE || NORETURN || MB]

[inst| enum Barriers =
    wmb || rmb || barrier || rcu_read_lock || rcu_read_unlock ||
    rcu_lock || rcu_unlock || sync_rcu ||
    before_atomic || after_atomic ||
    after_spinlock || after_unlock_lock ||
    after_srcu_read_unlock
]

-- Spot-check generated names
#check Accesses.ONCE
#check Accesses.RELEASE
#check Barriers.rcu_lock
#check Barriers.after_unlock_lock

[model| linux

enum Accesses = ONCE  ||
  RELEASE  ||
  ACQUIRE  ||
  NORETURN  ||
  MB
instructions R[Accesses]
instructions W[Accesses]
instructions RMW[Accesses]

enum Barriers = wmb  ||
  rmb  ||
  MB  ||
  barrier  ||
  rcu-lock   ||
  rcu-unlock  ||
  sync-rcu  ||
  before-atomic  ||
  after-atomic  ||
  after-spinlock  ||
  after-unlock-lock  ||
  after-srcu-read-unlock
instructions F[Barriers]


let FailedRMW = RMW \ (domain(rmw) | range(rmw))
let Acquire = ACQUIRE \ W \ FailedRMW
let Release = RELEASE \ R \ FailedRMW
let Mb = MB \ FailedRMW
let Noreturn = NORETURN \ W]
-- Check the instruction sets
