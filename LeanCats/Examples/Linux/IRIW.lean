import LeanCats.Basic
import LeanCats.Data
import LeanCats.CatParser.Macro
import LeanCats.Theorems

open Data
namespace LinuxLitmus

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

@[simp] abbrev initOpX : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 0) true false
@[simp] abbrev initOpY : Data.Effect :=
  Data.Effect.mk Data.Op.write y (some 0) true false
@[simp] abbrev wOpX1 : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 1) false false
@[simp] abbrev wOpY1 : Data.Effect :=
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
  Data.Event.mk 100 10 initOpX ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev initWy : Data.Event :=
  Data.Event.mk 101 10 initOpY ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev p0wX1 : Data.Event :=
  Data.Event.mk 1 0 wOpX1 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev p1rX1 : Data.Event :=
  Data.Event.mk 2 1 rOpX1 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev p1rY0 : Data.Event :=
  Data.Event.mk 3 1 rOpY0 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev p2wY1 : Data.Event :=
  Data.Event.mk 4 2 wOpY1 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev p3rY1 : Data.Event :=
  Data.Event.mk 5 3 rOpY1 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev p3rX0 : Data.Event :=
  Data.Event.mk 6 3 rOpX0 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev iriw_evts : Data.Events :=
  Data.Events.mk
    {initWx, initWy}
    {p1rX1, p1rY0, p3rY1, p3rX0}
    {initWx, initWy, p0wX1, p2wY1}
    {}
    {}
    {}

@[simp] def iriw_co : SetRel Event Event :=
  {(initWx, p0wX1), (initWy, p2wY1)}

instance : wellformed.co iriw_evts iriw_co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

@[simp] def iriw_rf : SetRel Event Event :=
  {(p0wX1, p1rX1), (initWy, p1rY0), (p2wY1, p3rY1), (initWx, p3rX0)}

@[simp] def iriw_rfInst : wellformed.rf iriw_evts iriw_rf :=
  Data.wellformed.rf.mk
    (by
      candidateExecution_wf
    )
    (by
      candidateExecution_wf
    )

@[simp] def iriw_mb : SetRel Event Event :=
  {(p1rX1, p1rY0), (p3rY1, p3rX0)}

@[simp] def iriw_test : CandidateExecution iriw_evts :=
  {
    evts := iriw_evts
    po' := iriw_evts.po
    prePo := instWellformedPo iriw_evts
    rf' := iriw_rf
    rfInst := iriw_rfInst
    co' := iriw_co
    rmw' := ∅
    preRMW := instWellformedRmwEmpty iriw_evts
    mb' := iriw_mb
    idUnique := uniqueId_by_id
    syncInF := by
      intro e h
      contradiction
    rfiPo := by
      candidateExecution_wf
  }

private lemma marked_self (e : Event) (he : e ∈ lkmm.Marked iriw_evts iriw_test) :
    (e, e) ∈ SetRel.mkId (lkmm.Marked iriw_evts iriw_test) := by
  exact ⟨rfl, he⟩

private lemma marked_of_once {e : Event} (he : e ∈ lkmm.ONCE iriw_evts iriw_test) :
    e ∈ lkmm.Marked iriw_evts iriw_test := by
    sorry


private lemma marked_self_of_once {e : Event} (he : e ∈ lkmm.ONCE iriw_evts iriw_test) :
    (e, e) ∈ SetRel.mkId (lkmm.Marked iriw_evts iriw_test) := by
  exact marked_self e (marked_of_once he)

private lemma prop_p1rY0_p3rY1 : (p1rY0, p3rY1) ∈ lkmm.prop iriw_evts iriw_test := by
  refine ⟨p1rY0, ?_, ?_⟩
  · exact marked_self_of_once (by simp [lkmm.ONCE])
  · refine ⟨p2wY1, ?_, ?_⟩
    · left
      refine ⟨?_, ?_⟩
      · right
        exact ⟨initWy, by simp [SetRel.inv, iriw_rf], by simp [iriw_co]⟩
      · simp [CatRel.Rel.external, CatRel.Rel.internal]
    · refine ⟨p2wY1, ?_, ?_⟩
      · right
        rfl
      · refine ⟨p2wY1, ?_, ?_⟩
        · exact marked_self_of_once (by simp [lkmm.ONCE])
        · refine ⟨p3rY1, ?_, ?_⟩
          · left
            exact ⟨by simp [iriw_rf], by simp [CatRel.Rel.external, CatRel.Rel.internal]⟩
          · exact marked_self_of_once (by simp [lkmm.ONCE])

private lemma prop_p3rX0_p1rX1 : (p3rX0, p1rX1) ∈ lkmm.prop iriw_evts iriw_test := by
  refine ⟨p3rX0, ?_, ?_⟩
  · exact marked_self_of_once (by simp [lkmm.ONCE])
  · refine ⟨p0wX1, ?_, ?_⟩
    · left
      refine ⟨?_, ?_⟩
      · right
        exact ⟨initWx, by simp [SetRel.inv, iriw_rf], by simp [iriw_co]⟩
      · simp [CatRel.Rel.external, CatRel.Rel.internal]
    · refine ⟨p0wX1, ?_, ?_⟩
      · right
        rfl
      · refine ⟨p0wX1, ?_, ?_⟩
        · exact marked_self_of_once (by simp [lkmm.ONCE])
        · refine ⟨p1rX1, ?_, ?_⟩
          · left
            exact ⟨by simp [iriw_rf], by simp [CatRel.Rel.external, CatRel.Rel.internal]⟩
          · exact marked_self_of_once (by simp [lkmm.ONCE])

private lemma pb_p1rY0_p3rX0 : (p1rY0, p3rX0) ∈ lkmm.pb iriw_evts iriw_test := by
  refine ⟨p3rY1, prop_p1rY0_p3rY1, ?_⟩
  refine ⟨p3rX0, ?_, ?_⟩
  · simp [lkmm.strong_fence, iriw_mb]
  · refine ⟨p3rX0, ?_, ?_⟩
    · right
      rfl
    · exact marked_self_of_once (by simp [lkmm.ONCE])

private lemma pb_p3rX0_p1rY0 : (p3rX0, p1rY0) ∈ lkmm.pb iriw_evts iriw_test := by
  refine ⟨p1rX1, prop_p3rX0_p1rX1, ?_⟩
  refine ⟨p1rY0, ?_, ?_⟩
  · simp [lkmm.strong_fence, iriw_mb]
  · refine ⟨p1rY0, ?_, ?_⟩
    · right
      rfl
    · exact marked_self_of_once (by simp [lkmm.ONCE])

theorem iriw_disallowed : ¬ lkmm.propagation iriw_evts iriw_test := by
  intro hprop
  unfold lkmm.propagation at hprop
  apply hprop p1rY0
  exact Relation.TransGen.head pb_p1rY0_p3rX0 (Relation.TransGen.single pb_p3rX0_p1rY0)

end LinuxLitmus
