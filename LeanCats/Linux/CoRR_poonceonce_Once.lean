import LeanCats.Basic
import LeanCats.Data
import LeanCats.Macro
import LeanCats.Theorems

open Data
namespace LinuxLitmus

instance instWellformedRmwEmpty (evts : Data.Events) : wellformed.rmw evts (∅ : SetRel Event Event) := by
  intro e h
  contradiction

abbrev x := 0

@[simp] abbrev initOpX : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 0) true false
@[simp] abbrev wOpX : Data.Effect :=
  Data.Effect.mk Data.Op.write x (some 1) false false
@[simp] abbrev rOpX1 : Data.Effect :=
  Data.Effect.mk Data.Op.read x (some 1) false false
@[simp] abbrev rOpX0 : Data.Effect :=
  Data.Effect.mk Data.Op.read x (some 0) false false

@[simp] abbrev initWx : Data.Event :=
  Data.Event.mk 100 10 initOpX ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev p0wX : Data.Event :=
  Data.Event.mk 1 0 wOpX ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev p1r0 : Data.Event :=
  Data.Event.mk 2 1 rOpX1 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩
@[simp] abbrev p1r1 : Data.Event :=
  Data.Event.mk 3 1 rOpX0 ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩

@[simp] abbrev corr_evts : Data.Events :=
  Data.Events.mk {initWx} {p1r0, p1r1} {initWx, p0wX} {} {} {}

@[simp] def corr_co : SetRel Event Event := {(initWx, p0wX)}
@[simp] def corr_po : SetRel Event Event := {(p1r0, p1r1)}

instance : wellformed.co corr_evts corr_co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

/-- C CoRR+poonceonce+Once

P0: WRITE_ONCE(*x, 1)
P1: r0 = READ_ONCE(*x); r1 = READ_ONCE(*x)
Outcome: witness uses `r0=1 ∧ r1=0`.

Chosen rf edges: `p0wX -> p1r0` and `initWx -> p1r1`. -/
@[simp] def corr_rf : SetRel Event Event := {(p0wX, p1r0), (initWx, p1r1)}

@[simp] def corr_rfInst : wellformed.rf corr_evts corr_rf :=
  Data.wellformed.rf.mk
    (by
      candidateExecution_wf
    )
    (by
      candidateExecution_wf
    )

def corr_test : CandidateExecution corr_evts :=
  {
    evts := corr_evts
    po' := corr_po
    prePo := by candidateExecution_wf
    rf' := corr_rf
    rfInst := corr_rfInst
    co' := corr_co
    rmw' := ∅
    preRMW := instWellformedRmwEmpty corr_evts
    syncInF := by
      intro e h
      contradiction
    idUnique := uniqueId_by_id
    rfiPo := by
      candidateExecution_wf
  }

theorem corr_FindCycle : ¬ (lkmm.coherence corr_evts corr_test) := by
  intro hacyc
  let rel : SetRel Event Event := po_loc corr_evts corr_test ∪ lkmm.com corr_evts corr_test
  have hrf0 : (initWx, p1r1) ∈ rel := by
    right
    left
    simp [corr_test, corr_rf]
  have hfr : (p1r1, p0wX) ∈ rel := by
    right
    right
    right
    refine ⟨initWx, ?_, ?_⟩
    · have hrf0' : (initWx, p1r1) ∈ corr_test.rf' := by
        simp [corr_test, corr_rf]
      simpa [SetRel.inv] using hrf0'
    · simp [corr_test, corr_co]
  have hrf1 : (p0wX, p1r0) ∈ rel := by
    right
    left
    simp [corr_test, corr_rf]
  have hpo : (p1r0, p1r1) ∈ rel := by
    left
    exact ⟨by simp [corr_test, corr_po], by simp⟩
  have hcycle : Relation.TransGen (fun x y => (x, y) ∈ rel) p1r1 p1r1 :=
    .head hfr (.head hrf1 (.single hpo))
  exact hacyc p1r1 (by simpa [rel, lkmm.coherence] using hcycle)

end LinuxLitmus
