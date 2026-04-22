import LeanCats.Basic
import LeanCats.Data
import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

defcat <"mips.cat">

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
@[simp] abbrev p0rX1 : Data.Event :=
  Data.Event.mk 2 0 rOpX1 ⟨Normal, Normal.none⟩
@[simp] abbrev p0rY0 : Data.Event :=
  Data.Event.mk 3 0 rOpY0 ⟨Normal, Normal.none⟩

@[simp] abbrev p1wY : Data.Event :=
  Data.Event.mk 4 1 wOpY ⟨Normal, Normal.none⟩
@[simp] abbrev p1rY1 : Data.Event :=
  Data.Event.mk 5 1 rOpY1 ⟨Normal, Normal.none⟩
@[simp] abbrev p1rX0 : Data.Event :=
  Data.Event.mk 6 1 rOpX0 ⟨Normal, Normal.none⟩

/-- X86 SB+rfi-pos

P0: W(x)=1; R(x)=1; R(y)=0
P1: W(y)=1; R(y)=1; R(x)=0 -/
@[simp] abbrev sbrfi_evts : Data.Events :=
  Data.Events.mk
    {initWx, initWy}
    {p0rX1, p0rY0, p1rY1, p1rX0}
    {initWx, initWy, p0wX, p1wY}
    {}
    {}
    {}

@[simp] def sbrfi_co : SetRel Event Event :=
  {(initWx, p0wX), (initWy, p1wY)}

instance : wellformed.co sbrfi_evts sbrfi_co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

/-- rf edges encode the expected outcome:
  - rfi: p0wX -> p0rX1 and p1wY -> p1rY1
  - reads of 0 from init writes: initWy -> p0rY0 and initWx -> p1rX0 -/
@[simp] def sbrfi_rf : SetRel Event Event :=
  {(p0wX, p0rX1), (p1wY, p1rY1), (initWy, p0rY0), (initWx, p1rX0)}

@[simp] def sbrfi_rfInst : wellformed.rf sbrfi_evts sbrfi_rf :=
  Data.wellformed.rf.mk
    (by
      candidateExecution_wf
    )
    (by
      candidateExecution_wf
    )

@[simp] def sbrfi_test : CandidateExecution sbrfi_evts :=
  {
    evts := sbrfi_evts
    po' := sbrfi_evts.po
    prePo := instWellformedPo sbrfi_evts
    rf' := sbrfi_rf
    rfInst := sbrfi_rfInst
    co' := sbrfi_co
    rmw' := ∅
    preRMW := instWellformedRmwEmpty sbrfi_evts
    idUnique := uniqueId_by_id
    syncInF := by
      intro e h
      contradiction
    rfiPo := by
      intro w r hrf htid
      simp [sbrfi_rf] at hrf
      rcases hrf with h | h | h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp [Data.Events.all], by simp [Data.Events.all], rfl, by decide⟩
      · rcases h with ⟨rfl, rfl⟩
        simp at htid
      · rcases h with ⟨rfl, rfl⟩
        simp at htid
  }
