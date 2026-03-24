import Mathlib.Data.Rel

namespace Data

inductive Op : Type where
  | write : Op
  | read : Op
  | fence : Op
  | branch : Op
deriving Inhabited, BEq, Repr, DecidableEq

structure Effect : Type where
  op : Op
  location : Nat
  -- For read, the value can not be determined at the begining.
  value : Option Nat
  isFirstWrite : Bool
  isFinalWrite : Bool
deriving Inhabited, BEq, Repr, DecidableEq

structure EventId where
  id : Nat
deriving DecidableEq

structure Event where
  id : Nat   -- Unique identifier, consistent with program order for a given thread
  t_id : Nat      -- Thread ID
  effect : Effect -- Action performed
  tag : Σ tagType : Type, tagType

inductive RMW where
  | trmw

-- Unsafe.
axiom event_id_unique :
  ∀ e₁ e₂ : Event, e₁.id = e₂.id -> e₁ = e₂

instance : DecidableEq Event := by
  intro a b
  by_cases h : a.id = b.id
  · exact isTrue (event_id_unique a b h)
  · exact isFalse (by
      intro hEq
      have : a.id = b.id := by simp [hEq]
      exact h this)

instance : BEq Event where
  beq e1 e2 := e1.id == e2.id

inductive Normal where
| none : Normal

@[simp] def reads : Set Event :=
  λ e ↦ e.effect.op = Op.read

@[simp] def writes : Set Event :=
  λ e ↦ e.effect.op = Op.write

@[simp] def modifications : Set Event :=
  reads ∪ writes

-- Events can be (for brevity this is not an exhaustive list):
-- writes, gathered in the set W, including the the set IW of initial writes coming from the prelude of the program;
-- reads, gathered in the set R;
-- branch events, gathered in the set B;
-- fences, gathered in the set F.
-- this is the base events, because the CandidateExecution needs to extends it.
structure Events where
  (IW : Set Event)
  (R : Set Event)
  (W : Set Event)
  (B : Set Event)
  (F : Set Event)
  (RMW : Set Event)
  (M : Set Event)

@[simp] def Events.all (evts : Events) :=
  evts.IW ∪ evts.R ∪ evts.W ∪ evts.B ∪ evts.F ∪ evts.RMW ∪ evts.M

instance : Membership Event Events where
  mem := fun es e => e ∈ es.all

structure Events.preCo (evts : Events) (co : SetRel Event Event) : Prop where
  /-- Every pair in co consists of writes in evts at the same location. -/
  wellTyped : ∀ e₁ e₂ : Event, (e₁, e₂) ∈ co →
    e₁ ∈ evts.all
    ∧ e₂ ∈ evts.all
    ∧ e₁.effect.op = Op.write
    ∧ e₂.effect.op = Op.write
    ∧ e₁.effect.location = e₂.effect.location
  /-- co is total: any two distinct writes to the same location are co-ordered. -/
  total : ∀ e₁ e₂ : Event,
    e₁ ∈ evts.W → e₂ ∈ evts.W
    → e₁.effect.location = e₂.effect.location
    → e₁ ≠ e₂
    → (e₁, e₂) ∈ co ∨ (e₂, e₁) ∈ co

class wellformed.co (evts : Events) (corel : SetRel Event Event) : Prop where
  -- The Type is the Prop, and the proof is the term, do not use :=
  irrefl : ∀ e : Event, ¬ (e, e) ∈ corel
  trans : ∀ e₁ e₂ e₃, (e₁, e₂) ∈ corel -> (e₂, e₃) ∈ corel -> (e₁, e₃) ∈ corel
  preco : evts.preCo corel

@[simp] def wellformed.rmw (evts : Events) (rmw : SetRel Event Event) : Prop :=
  rmw ⊆ {(e₁, e₂) |
    e₁.tag = ⟨RMW, RMW.trmw⟩
    ∧ e₂.tag = ⟨RMW, RMW.trmw⟩
    ∧ e₁ ∈ evts.R
    ∧ e₂ ∈ evts.W
    ∧ e₁.effect.location = e₂.effect.location}

@[simp] def wellformed.rf (evts : Events) (rf : SetRel Event Event) : Prop :=
  ∀ (w r : Event), (w, r) ∈ rf ->
    w ∈ evts.W ∧ r ∈ evts.R
    ∧ w.effect.location = r.effect.location
    ∧ r.id ≠ w.id

@[simp] def wellformed.po (po : SetRel Event Event) : Prop :=
  ∀ x y z, (x, y) ∈ po -> (y, z) ∈ po -> (x, z) ∈ po

@[simp] def Events.po (evts : Events) : SetRel Event Event :=
  λ (a, b) =>
    a ∈ evts.all ∧ b ∈ evts.all ∧ a.t_id = b.t_id ∧ a.id < b.id

#check trichotomous

end Data
