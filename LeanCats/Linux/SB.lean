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

-- init x = 0
--
-- t0        t1
-- Wx = 1   Wx = 2
-- rX       rX

-- exists: rX0 = 2 ∧ rX1 = 1
-- The X86 allows this.
-- But mips doesn't

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
@[simp] abbrev rOpX0 : Data.Effect :=
  Data.Effect.mk Data.Op.read x (some 0) false false
@[simp] abbrev rOpY0 : Data.Effect :=
  Data.Effect.mk Data.Op.read y (some 0) false false

@[simp] abbrev initWx : Data.Event :=
  Data.Event.mk 100 10 initOpX ⟨Normal, Normal.none⟩
@[simp] abbrev initWy : Data.Event :=
  Data.Event.mk 101 10 initOpY ⟨Normal, Normal.none⟩

@[simp] abbrev p0wX : Data.Event :=
  Data.Event.mk 1 0 wOpX ⟨Normal, Normal.none⟩
@[simp] abbrev p0rY0 : Data.Event :=
  Data.Event.mk 3 0 rOpY0 ⟨Normal, Normal.none⟩

@[simp] abbrev p1wY : Data.Event :=
  Data.Event.mk 4 1 wOpY ⟨Normal, Normal.none⟩
@[simp] abbrev p1rX0 : Data.Event :=
  Data.Event.mk 6 1 rOpX0 ⟨Normal, Normal.none⟩

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
  {(initWy, p0rY0), (initWx, p1rX0)}

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
  apply hsc p0wX
  exact
    Relation.TransGen.head (a := p0wX) (b := p0rY0)
      (by
        left
        exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩)
      (Relation.TransGen.head (a := p0rY0) (b := p1wY)
        (by
          right
          right
          left
          exact ⟨initWy, by simp, by simp⟩)
        (Relation.TransGen.head (a := p1wY) (b := p1rX0)
          (by
            left
            exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩)
          (Relation.TransGen.single (a := p1rX0) (b := p0wX)
            (by
              right
              right
              left
              exact ⟨initWx, by simp, by simp⟩))))

theorem sb_tso : tsox.tso sb_evts sb_test :=
by
  simp only [tsox.tso]
  apply acyclic_of_rank (fun e => match e.id with
    | 100 => 0  -- initWx
    | 101 => 1  -- initWy
    | 3   => 2  -- p0rY0
    | 6   => 3  -- p1rX0
    | 4   => 4  -- p1wY
    | 1   => 5  -- p0wX
    | _   => 6)
  intro a b hab
  simp only [CatRel.CatUnion.union, CatRel.SetRel.union, Set.mem_setOf_eq,
             tsox.implied, tsox.xppo, tsox.At, rfe,
             CandidateExecution.fr', SetRel.inv, SetRel.comp,
             sb_test, sb_rf, sb_co, sb_evts,
             Data.Events.all, Data.Events.po, SetRel.mkId,
             CatRel.prod, Set.mem_prod, Set.prod,
             CatRel.W, CatRel.R,
             CatRel.Rel.external, CatRel.Rel.internal,
             Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
             Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
             Set.mem_preimage, Prod.swap,
             SetRel.dom, SetRel.cod, SetRel.dom_mkId,
             Prod.mk.injEq, Prod.fst, Prod.snd,
             and_false, false_and, false_or, or_false,
             not_true, not_false_eq_true,
             exists_false, exists_eq_left, exists_eq_left'] at hab
  -- implied is impossible since rmw = ∅
  rcases hab with ⟨mid, _, hmid_in | ⟨mid2, hmid2_in, _⟩⟩ | hab'
  · obtain ⟨_, h⟩ := hmid_in
    exact absurd h nofun
  · obtain ⟨_, h⟩ := hmid2_in
    exact absurd h nofun
  -- remaining: xppo ∨ rfe ∨ fr ∨ co
  rcases hab' with hxppo | (hrfe | (hfr | hco))
  · obtain ⟨hprod, hpo⟩ := hxppo
    simp only [Set.mem_setOf_eq] at hprod
    change a ∈ sb_evts.all ∧ b ∈ sb_evts.all ∧ a.t_id = b.t_id ∧ a.id < b.id at hpo
    obtain ⟨_, _, htid, hlt⟩ := hpo
    rcases hprod with (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
          simp_all
  · obtain ⟨hrf, htid⟩ := hrfe
    rcases hrf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · decide
    · decide
  · obtain ⟨w, hrf_inv, hco⟩ := hfr
    rcases hrf_inv with ⟨hw, ha⟩ | ⟨hw, ha⟩ <;>
      rcases hco with ⟨hw', hb⟩ | ⟨hw', hb⟩ <;>
        subst ha hb hw <;> simp_all <;> (try decide) <;> (try (subst hw'; decide))
  · rcases hco with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

example : mips.pso sb_evts sb_test :=
by
  exact mipsWeakerThanTso sb_evts sb_test sb_tso
