import LeanCats.Basic
import LeanCats.Data
import LeanCats.Macro
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
    uniqueId := uniqueId_by_id iriw_evts
    syncInF := by
      intro e h
      contradiction
    rfiPo := by
      candidateExecution_wf
  }

theorem iriw_disallowed : ¬ lkmm.propagation iriw_evts iriw_test := by
  native_decide

end LinuxLitmus
