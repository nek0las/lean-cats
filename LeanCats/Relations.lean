import LeanCats.Data

namespace CatRel
open Data

@[simp] def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
@[simp] def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y

-- Not sure if this is the correct definition of cartesian product.
def prod (s₁ s₂ : Set Event) : Rel Event Event := λ e₁ e₂ ↦ e₁ ∈ s₁ ∧ e₂ ∈ s₂

#check Rel.inv

instance instUnionRelEvents : Union (Event → Event → Prop) := ⟨union⟩
instance : Union (Rel Event Event) := instUnionRelEvents
instance : Inter (Rel Event Event) := ⟨inter⟩

@[simp] def domain (r : Rel Event Event) : Set Event := λ e ↦ ∃ e', r e e'

@[simp] def R : Set Event :=
  λ e ↦ e.effect.op = Op.read

@[simp] def W : Set Event :=
  λ e ↦ e.effect.op = Op.write

@[simp] def M : Set Event :=
  R ∪ W

@[simp] def Rel.prod (lhs rhs : Event -> Prop) : Rel Event Event :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

theorem RelProdIsSetProd (s₁ s₂ : Event -> Prop) (e₁ e₂ : Event) :
  Rel.prod s₁ s₂ e₁ e₂ = ((e₁, e₂) ∈ Set.prod s₁ s₂) :=
  by
    simp
    apply Iff.intro
    {
      intro hrel
      unfold Set.prod
      aesop
    }
    {
      intro hset
      aesop
    }

abbrev Acyclic (r : Rel Event Event) := ∀a : Event, ¬ Relation.TransGen r a a

@[simp] def Rel.internal (e₁ e₂ : Event) : Prop :=
  e₁.t_id = e₂.t_id

@[simp] def Rel.external (e₁ e₂ : Event) : Prop :=
  ¬ (Rel.internal e₁ e₂)

@[simp] def Rel.empty (_ _ : Event) : Prop :=
  False

@[simp] def Rel.loc (e₁ e₂ : Event) : Prop :=
  e₁.effect.location = e₂.effect.location

@[simp] def Rel.ext (e₁ e₂ : Event) : Prop :=
  e₁.t_id ≠ e₂.t_id

@[simp] def isWrite (e : Event) : Prop :=
  e.effect.op = Op.write

structure rf (evts : Events) (e₁ e₂ : Event) : Prop where
  -- left one in the evts.
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : e₁.effect.op = Op.write
  rRead : e₂.effect.op = Op.read
  sameTarget : e₁.effect.location = e₂.effect.location

@[simp] def internal (evts : Events) : Rel Event Event :=
  λ e₁ e₂ ↦ e₁ ∈ evts ∧ e₂ ∈ evts ∧ e₁.t_id = e₂.t_id

@[simp] def external (evts : Events) : Rel Event Event :=
  λ e₁ e₂ ↦ ¬(internal evts e₁ e₂)

@[simp] def isWriteSameLoc (l : Location) (e : Event) :=
  e.effect.op = Op.write ∧ e.effect.location = l

def po (evts : Events) (e₁ e₂ : Event) : Prop :=
  internal evts e₁ e₂ ∧ e₁.id < e₂.id

instance (evts : Events) : IsStrictOrder Event (rf evts) where
  irrefl :=
  by
    intro e
    intro hin
    have h₁ : e.effect.op = Op.write := by apply hin.lWrite
    have h₂ : e.effect.op = Op.read := by apply hin.rRead
    rw [h₁] at h₂
    contradiction
  trans :=
  by
    intro a b c
    intro hrfab
    intro hrfbc
    have lIn : a ∈ evts := by apply hrfab.lIn
    have rIn : c ∈ evts := by apply hrfbc.rIn
    have lWrite : a.effect.op = Op.write := by apply hrfab.lWrite
    have rRead : c.effect.op = Op.read := by apply hrfbc.rRead
    have sameTarget : a.effect.location = c.effect.location :=
    by
      have abSameTarget : a.effect.location = b.effect.location := by apply hrfab.sameTarget
      have bcSameTarget : b.effect.location = c.effect.location := by apply hrfbc.sameTarget
      rw [abSameTarget]
      rw [bcSameTarget]

    exact ⟨lIn, rIn, lWrite, rRead, sameTarget⟩

theorem rfIsTransitive {evts : Events} : Transitive (rf evts) :=
  by
    intro a b c
    intro rab rbc
    obtain ⟨lInab, rInab, lWriteab, rReadab, sameTargetab⟩ := rab
    obtain ⟨lInbc, rInbc, lWritebc, rReadbc, sameTargetbc⟩ := rbc
    rw [<-sameTargetab] at sameTargetbc
    exact ⟨lInab, rInbc, lWriteab, rReadbc, sameTargetbc⟩

-- This defines:
-- Write event must exists
-- Write equlity (If the two write events write to the same read event, then these two writes are the same)
structure rf.wellformed (evts : Events) (e₁ e₂ : Event) extends rf evts e₁ e₂ where
  wExtAndUnique {r} : r.effect.op = Op.read ->
    (∃w, isWrite w ∧ rf evts w r)
    ∧ (∀ w₁ w₂, rf evts w₁ r -> rf evts w₂ r -> w₁ = w₂)

structure preCo (evts : Events) (e₁ e₂ : Event) : Prop where
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : isWrite e₁
  rWrite : isWrite e₂

-- TODO: Check if this definition follows the Coq definition in diy7.
structure co.wellformed
  (evts : Events)
  [IsStrictTotalOrder Event (preCo evts)]
  (e₁ e₂ : Event)
  extends preCo evts e₁ e₂

@[simp] def fr
  (evts : Events)
  [IsStrictTotalOrder Event (preCo evts)]
  (e1 e2 : Event)
  : Prop :=
  ∃w, isWrite w ∧ rf evts w e1 ∧ co.wellformed evts w e2


def com
  (evts : Events)
  [IsStrictTotalOrder Event (preCo evts)]
  (e₁ e₂ : Event) :=
  rf.wellformed evts e₁ e₂ ∨ co.wellformed evts e₁ e₂ ∨ fr evts e₁ e₂

#check Rel.prod

end CatRel
