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

structure Event where
  id : Nat   -- Unique identifier, consistent with program order for a given thread
  t_id : Nat      -- Thread ID
  effect : Effect -- Action performed
  tag : Σ tagType : Type, tagType

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
structure Events where
  (IW : Set Event)
  (R : Set Event)
  (W : Set Event)
  (B : Set Event)
  (F : Set Event)
  (RMW : Set Event)
  (SRCU : Set Event)
  (M : Set Event)

def Events.all (evts : Events) :=
  evts.IW ∪ evts.R ∪ evts.W ∪ evts.B ∪ evts.F ∪ evts.RMW ∪ evts.SRCU ∪ evts.M

instance : Membership Event Events where
  mem := fun es e => e ∈ es.all

-- We can derive some relations based on the events.
@[simp] def Events.rf (evts : Events) : SetRel Event Event :=
  λ (w, r) =>
    w ∈ evts.W ∧ r ∈ evts.R
    ∧ w.effect.location = r.effect.location
    ∧ r.effect.value = w.effect.value
    ∧ r.id ≠ w.id

@[simp] def Events.po (evts : Events) : SetRel Event Event :=
  λ (a, b) =>
    a ∈ evts ∧ b ∈ evts ∧ a.t_id = b.t_id ∧ a.id < b.id

/-
In the definition of the cat specification, we know that the tag is just an id.
Basically it's a event.

What we want is a:
  enum A = 'z | 'a
  enum B = 'z | 'a
  etc

-/

end Data
