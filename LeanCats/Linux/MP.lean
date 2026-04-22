import LeanCats.Basic
import LeanCats.Data
import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Relations
import LeanCats.Theorems

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
@[simp] abbrev wOpX1 : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 1) false false
@[simp] abbrev wOpY1 : Data.Effect :=
  Data.Effect.mk Data.Op.write y (some 1) false false
@[simp] abbrev rOpY1 : Data.Effect :=
  Data.Effect.mk Data.Op.read y (some 1) false false
@[simp] abbrev rOpX0 : Data.Effect :=
  Data.Effect.mk Data.Op.read x (some 0) false false

@[simp] abbrev initWx : Data.Event :=
  Data.Event.mk 100 10 initOpX ⟨Normal, Normal.none⟩
@[simp] abbrev initWy : Data.Event :=
  Data.Event.mk 101 10 initOpY ⟨Normal, Normal.none⟩

@[simp] abbrev p0wX1 : Data.Event :=
  Data.Event.mk 1 0 wOpX1 ⟨Normal, Normal.none⟩
@[simp] abbrev p0wY1 : Data.Event :=
  Data.Event.mk 2 0 wOpY1 ⟨Normal, Normal.none⟩

@[simp] abbrev p1rY1 : Data.Event :=
  Data.Event.mk 3 1 rOpY1 ⟨Normal, Normal.none⟩
@[simp] abbrev p1rX0 : Data.Event :=
  Data.Event.mk 4 1 rOpX0 ⟨Normal, Normal.none⟩

/-- MP outcome: P0 writes x then y; P1 reads y=1 then x=0. -/
@[simp] abbrev mp_evts : Data.Events :=
  Data.Events.mk
    {initWx, initWy}
    {p1rY1, p1rX0}
    {initWx, initWy, p0wX1, p0wY1}
    {}
    {}
    {}

@[simp] def mp_co : SetRel Event Event :=
  {(initWx, p0wX1), (initWy, p0wY1)}

instance : wellformed.co mp_evts mp_co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

@[simp] def mp_rf : SetRel Event Event :=
  {(p0wY1, p1rY1), (initWx, p1rX0)}

@[simp] def mp_rfInst : wellformed.rf mp_evts mp_rf :=
  Data.wellformed.rf.mk
    (by
      candidateExecution_wf
    )
    (by
      candidateExecution_wf
    )

@[simp] def mp_test : CandidateExecution mp_evts :=
  {
    evts := mp_evts
    po' := mp_evts.po
    prePo := instWellformedPo mp_evts
    rf' := mp_rf
    rfInst := mp_rfInst
    co' := mp_co
    rmw' := ∅
    preRMW := instWellformedRmwEmpty mp_evts
    idUnique := uniqueId_by_id
    syncInF := by
      intro e h
      contradiction
    rfiPo := by
      candidateExecution_wf
  }

defcat <"mips.cat">
defcat <"tsox.cat">

theorem mp_tso_disallowed : ¬ tsox.tso mp_evts mp_test := by
  intro htso
  unfold tsox.tso at htso
  let rtso : SetRel Data.Event Data.Event :=
    CatRel.CatUnion.union (tsox.implied mp_evts mp_test)
      (CatRel.CatUnion.union (tsox.xppo mp_evts mp_test)
        (CatRel.CatUnion.union (rfe mp_evts mp_test)
          (CatRel.CatUnion.union mp_test.fr' mp_test.co')))

  have h1xppo : (p0wX1, p0wY1) ∈ tsox.xppo mp_evts mp_test := by
    refine ⟨?_, ?_⟩
    · exact Or.inl ⟨by simp, by simp⟩
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩

  have h2rfe : (p0wY1, p1rY1) ∈ rfe mp_evts mp_test := by
    refine ⟨?_, ?_⟩
    · simp [mp_test, mp_rf]
    · simp [CatRel.Rel.external]

  have h3xppo : (p1rY1, p1rX0) ∈ tsox.xppo mp_evts mp_test := by
    refine ⟨?_, ?_⟩
    · exact Or.inr (Or.inr ⟨by simp, by simp⟩)
    · exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩

  have h4fr : (p1rX0, p0wX1) ∈ mp_test.fr' := by
    refine ⟨initWx, ?_, ?_⟩
    · simp [mp_test, mp_rf, SetRel.inv]
    · simp [mp_test, mp_co]

  have h1 : (p0wX1, p0wY1) ∈ rtso := by exact Or.inr (Or.inl h1xppo)
  have h2 : (p0wY1, p1rY1) ∈ rtso := by exact Or.inr (Or.inr (Or.inl h2rfe))
  have h3 : (p1rY1, p1rX0) ∈ rtso := by exact Or.inr (Or.inl h3xppo)
  have h4 : (p1rX0, p0wX1) ∈ rtso := by exact Or.inr (Or.inr (Or.inr (Or.inl h4fr)))

  apply htso p0wX1
  exact Relation.TransGen.head h1
    (Relation.TransGen.head h2
      (Relation.TransGen.head h3
        (Relation.TransGen.single h4)))

theorem mp_mips_allowed : mips.pso mp_evts mp_test := by
  simp only [mips.pso]
  apply acyclic_of_rank (fun e => match e.id with
    | 100 => 0  -- initWx
    | 101 => 1  -- initWy
    | 2   => 2  -- p0wY1
    | 3   => 3  -- p1rY1
    | 4   => 4  -- p1rX0
    | 1   => 5  -- p0wX1
    | _   => 6)
  intro a b hab
  simp only [CatRel.CatUnion.union, CatRel.SetRel.union, Set.mem_setOf_eq,
             mips.ppo, rfe,
             CandidateExecution.fr', SetRel.inv, SetRel.comp,
             mp_test, mp_rf, mp_co, mp_evts,
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
  rcases hab with hppo | (hrfe | (hfr | hco))
  · obtain ⟨hpo, hppo_core⟩ := hppo
    change a ∈ mp_evts.all ∧ b ∈ mp_evts.all ∧ a.t_id = b.t_id ∧ a.id < b.id at hpo
    obtain ⟨_, _, htid, hlt⟩ := hpo
    rcases hppo_core with ⟨haR, hbM⟩ | hsync
    · rcases haR with rfl | rfl
      · rcases hbM with hbR | hbW
        · rcases hbR with rfl | rfl <;> simp_all
        · rcases hbW with rfl | rfl | rfl | rfl <;> simp_all
      · rcases hbM with hbR | hbW
        · rcases hbR with rfl | rfl <;> simp_all
        · rcases hbW with rfl | rfl | rfl | rfl <;> simp_all
    · rcases hsync with ⟨mid, hsync_amid, _⟩
      have hmidSync : mid ∈ mp_test.SYNC' := by
        simpa [CatRel.prod, SetRel.dom_mkId] using hsync_amid.2.2
      simp [mp_test] at hmidSync
  · obtain ⟨hrf, htid⟩ := hrfe
    rcases hrf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · decide
    · decide
  · obtain ⟨w, hrf_inv, hco_wb⟩ := hfr
    simp [SetRel.inv, mp_rf, mp_co] at hrf_inv hco_wb
    rcases hrf_inv with ⟨hw, ha⟩ | ⟨hw, ha⟩
    · rcases hco_wb with ⟨hw', hb⟩ | ⟨hw', hb⟩
      · subst ha hb hw
        cases hw' <;> try decide
      · subst ha hb hw
        cases hw' <;> try decide
    · rcases hco_wb with ⟨hw', hb⟩ | ⟨hw', hb⟩
      · subst ha hb hw
        cases hw' <;> try decide
      · subst ha hb hw
        cases hw' <;> try decide
  · rcases hco with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end Litmus
