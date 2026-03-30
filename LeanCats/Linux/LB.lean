import LeanCats.Basic
import LeanCats.Data
import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic
import LeanCats.mipsWeakerThanTSO

-- In this litmus test, we want to show that sometimes the X86 is weaker than mips because of the sc-per-location.

-- init x = 0, y = 0
--
-- rX       rY
-- Wy=1     rX=1

-- exists: rX0 = 1 ∧ rX1 = 1

open Data

namespace Litmus


instance instWellformedPo (evts : Data.Events) : wellformed.po evts.po := by
  intro x y z hxy hyz
  rcases hxy with ⟨hx, hy, hxyTid, hxyLt⟩
  rcases hyz with ⟨_, hz, hyzTid, hyzLt⟩
  exact ⟨hx, hz, Eq.trans hxyTid hyzTid, Nat.lt_trans hxyLt hyzLt⟩

instance instWellformedRmwEmpty (evts : Data.Events) : wellformed.rmw evts (∅ : SetRel Event Event) := by
  intro e h
  contradiction

abbrev x := 0
abbrev y := 1

inductive Normal where
| none : Normal

@[simp] abbrev initOpX : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 0) true false
@[simp] abbrev initOpY : Data.Effect :=
  Data.Effect.mk Data.Op.write y (some 0) true false
@[simp] abbrev wOpX : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 1) false false
@[simp] abbrev wOpY : Data.Effect :=
  Data.Effect.mk Data.Op.write y (some 1) false false
@[simp] abbrev rOpX1 : Data.Effect :=
  Data.Effect.mk Data.Op.read x (some 1) false false
@[simp] abbrev rOpY1 : Data.Effect :=
  Data.Effect.mk Data.Op.read y (some 1) false false

@[simp] abbrev initWx : Data.Event :=
  Data.Event.mk 100 10 initOpX ⟨Normal, Normal.none⟩
@[simp] abbrev initWy : Data.Event :=
  Data.Event.mk 101 10 initOpY ⟨Normal, Normal.none⟩

@[simp] abbrev p0wX : Data.Event :=
  Data.Event.mk 3 0 wOpX ⟨Normal, Normal.none⟩
@[simp] abbrev p0rY0 : Data.Event :=
  Data.Event.mk 1 0 rOpY1 ⟨Normal, Normal.none⟩

@[simp] abbrev p1wY : Data.Event :=
  Data.Event.mk 6 1 wOpY ⟨Normal, Normal.none⟩
@[simp] abbrev p1rX0 : Data.Event :=
  Data.Event.mk 4 1 rOpX1 ⟨Normal, Normal.none⟩

/-- X86 SB+rfi-pos

P0: W(x)=1; R(x)=1; R(y)=0
P1: W(y)=1; R(y)=1; R(x)=0 -/
@[simp] abbrev sb_evts : Data.Events :=
  Data.Events.mk
    {initWx, initWy}
    {p0rY0, p1rX0}
    {initWx, initWy, p0wX, p1wY}
    {}
    {}
    {}

@[simp] def sb_co : SetRel Event Event :=
  {(initWx, p0wX), (initWy, p1wY)}

instance : wellformed.co sb_evts sb_co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

/-- rf edges encode the expected outcome:
  - rfi: p0wX -> p0rX1 and p1wY -> p1rY1
  - reads of 0 from init writes: initWy -> p0rY0 and initWx -> p1rX0 -/
@[simp] def sb_rf : SetRel Event Event :=
  {(p1wY, p0rY0), (p0wX, p1rX0)}

@[simp] def sb_rfInst : wellformed.rf sb_evts sb_rf :=
  Data.wellformed.rf.mk
    (by
      candidateExecution_wf
    )
    (by
      candidateExecution_wf
    )

@[simp] def sb_test : CandidateExecution sb_evts :=
  {
    evts := sb_evts
    po' := sb_evts.po
    prePo := instWellformedPo sb_evts
    rf' := sb_rf
    rfInst := sb_rfInst
    co' := sb_co
    rmw' := ∅
    preRMW := instWellformedRmwEmpty sb_evts
    uniqueId := uniqueId_by_id sb_evts
    syncInF := by
      intro e h
      contradiction
    rfiPo := by
      candidateExecution_wf
  }

defcat <"mips.cat">
defcat <"tsox.cat">
defcat <"sc.cat">

example : ¬ sc.sc sb_evts sb_test :=
by
  intro hsc
  simp [sc.sc, CatRel.CatUnion.union, sb_test, sb_rf, sb_co, CandidateExecution.fr', SetRel.comp, SetRel.inv] at hsc
  apply hsc p0rY0
  exact
    Relation.TransGen.head (a := p0rY0) (b := p0wX)
      (by
        left
        exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩)
      (Relation.TransGen.head (a := p0wX) (b := p1rX0)
        (by
          right
          left
          simp)
        (Relation.TransGen.head (a := p1rX0) (b := p1wY)
          (by
            left
            exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩)
          (Relation.TransGen.single (a := p1wY) (b := p0rY0)
            (by
              right
              left
              simp))))

theorem sb_tso : ¬ tsox.tso sb_evts sb_test :=
by
  intro htso
  unfold tsox.tso at htso
  let rtso : SetRel Data.Event Data.Event :=
    CatRel.CatUnion.union (tsox.implied sb_evts sb_test)
      (CatRel.CatUnion.union (tsox.xppo sb_evts sb_test)
        (CatRel.CatUnion.union (rfe sb_evts sb_test)
          (CatRel.CatUnion.union sb_test.fr' sb_test.co')))
  have h1xppo : (p0rY0, p0wX) ∈ tsox.xppo sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
  have h2rfe : (p0wX, p1rX0) ∈ rfe sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · simp [sb_test, sb_rf]
    · simp [CatRel.Rel.external]
  have h3xppo : (p1rX0, p1wY) ∈ tsox.xppo sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
  have h4rfe : (p1wY, p0rY0) ∈ rfe sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · simp [sb_test, sb_rf]
    · simp [CatRel.Rel.external]
  have h1 : (p0rY0, p0wX) ∈ rtso := by exact Or.inr (Or.inl h1xppo)
  have h2 : (p0wX, p1rX0) ∈ rtso := by exact Or.inr (Or.inr (Or.inl h2rfe))
  have h3 : (p1rX0, p1wY) ∈ rtso := by exact Or.inr (Or.inl h3xppo)
  have h4 : (p1wY, p0rY0) ∈ rtso := by exact Or.inr (Or.inr (Or.inl h4rfe))
  apply htso p0rY0
  exact Relation.TransGen.head h1 (Relation.TransGen.head h2 (Relation.TransGen.head h3 (Relation.TransGen.single h4)))

example : ¬ mips.pso sb_evts sb_test :=
by
  intro hmips
  have hacyc : CatRel.SetRel.Acyclic
      (CatRel.CatUnion.union (mips.ppo sb_evts sb_test)
        (CatRel.CatUnion.union (rfe sb_evts sb_test)
          (CatRel.CatUnion.union sb_test.fr' sb_test.co'))) := by
    simpa [mips.pso, CatRel.CatUnion.union] using hmips

  have h1ppo : (p0rY0, p0wX) ∈ mips.ppo sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
    · left
      exact ⟨by simp, Or.inr (by simp)⟩
  have h2rfe : (p0wX, p1rX0) ∈ rfe sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · simp [sb_test, sb_rf]
    · simp [CatRel.Rel.external]
  have h3ppo : (p1rX0, p1wY) ∈ mips.ppo sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
    · left
      exact ⟨by simp, Or.inr (by simp)⟩
  have h4rfe : (p1wY, p0rY0) ∈ rfe sb_evts sb_test := by
    refine ⟨?_, ?_⟩
    · simp [sb_test, sb_rf]
    · simp [CatRel.Rel.external]

  have h1 : (p0rY0, p0wX) ∈ CatRel.CatUnion.union (mips.ppo sb_evts sb_test)
      (CatRel.CatUnion.union (rfe sb_evts sb_test)
        (CatRel.CatUnion.union sb_test.fr' sb_test.co')) := by
    exact Or.inl h1ppo
  have h2 : (p0wX, p1rX0) ∈ CatRel.CatUnion.union (mips.ppo sb_evts sb_test)
      (CatRel.CatUnion.union (rfe sb_evts sb_test)
        (CatRel.CatUnion.union sb_test.fr' sb_test.co')) := by
    exact Or.inr (Or.inl h2rfe)
  have h3 : (p1rX0, p1wY) ∈ CatRel.CatUnion.union (mips.ppo sb_evts sb_test)
      (CatRel.CatUnion.union (rfe sb_evts sb_test)
        (CatRel.CatUnion.union sb_test.fr' sb_test.co')) := by
    exact Or.inl h3ppo
  have h4 : (p1wY, p0rY0) ∈ CatRel.CatUnion.union (mips.ppo sb_evts sb_test)
      (CatRel.CatUnion.union (rfe sb_evts sb_test)
        (CatRel.CatUnion.union sb_test.fr' sb_test.co')) := by
    exact Or.inr (Or.inl h4rfe)

  apply hacyc p0rY0
  exact Relation.TransGen.head h1 (Relation.TransGen.head h2 (Relation.TransGen.head h3 (Relation.TransGen.single h4)))
