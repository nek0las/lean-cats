-- In this file, we define a serias of instructions to prove if it's allowed or not regarding to a specific model.
import LeanCats.Basic
import LeanCats.Data
open Data
namespace Litmus

instance instWellformedPo (evts : Data.Events) : wellformed.po evts.po := by
  intro x y z hxy hyz
  rcases hxy with ⟨hx, hy, hxyTid, hxyLt⟩
  rcases hyz with ⟨_, hz, hyzTid, hyzLt⟩
  exact ⟨hx, hz, Eq.trans hxyTid hyzTid, Nat.lt_trans hxyLt hyzLt⟩

instance instWellformedRmwEmpty (evts : Data.Events) : wellformed.rmw evts (∅ : SetRel Event Event) := by
  intro e h
  exact False.elim h
-- X86 SB
-- "Fre PodWR Fre PodWR"
-- { x=0; y=0; }
--  P0              | P1          ;
--  (1) MOV [x],$1  | (3) MOV [y],$1  ;
--  (2) MOV EAX,[y] | (4) MOV EAX,[x] ;
--
-- exists (0:EAX=0 /\ 1:EAX=0)
-- One simple storing-buffer generated for one candidate execution.
-- The insturction (1) and (3) are reads and (2) and (4) are writes.
-- So we could define these two instructions in Lean 4 by:

inductive Normal where
  | none : Normal

abbrev x := 0
abbrev y := 1

-- Exists (0:EAX=0 ∧ 1:EAX=0)
@[simp] abbrev initOpX : Data.Effect := { op := Data.Op.write, location := x, value := some 0, isFinalWrite := false, isFirstWrite := true }
@[simp] abbrev initOpY : Data.Effect := { op := Data.Op.write, location := y, value := some 0, isFinalWrite := false, isFirstWrite := true }
@[simp] abbrev rOpX : Data.Effect := { op := Data.Op.read, location := x, value := none, isFinalWrite := false, isFirstWrite := false}
@[simp] abbrev wOpX : Data.Effect := { op := Data.Op.write, location := x, value := some 1, isFinalWrite := false, isFirstWrite := false }
@[simp] abbrev rOpY : Data.Effect := { op := Data.Op.read, location := y, value := none, isFinalWrite := false, isFirstWrite := false }
@[simp] abbrev wOpY : Data.Effect := { op := Data.Op.write, location := y, value := some 1, isFinalWrite := false, isFirstWrite := false }

@[simp] abbrev initWx : Data.Event := { id := 10, t_id := 10, effect := initOpX, tag := ⟨Normal, Normal.none⟩}
@[simp] abbrev initWy : Data.Event := { id := 11, t_id := 10, effect := initOpY, tag := ⟨Normal, Normal.none⟩}
@[simp] abbrev inst1writeX : Data.Event := { id := 1, t_id := 0, effect := wOpX, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev inst2readY : Data.Event := { id := 2, t_id := 0, effect := rOpY, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev inst3writeY : Data.Event := { id := 3, t_id := 1, effect := wOpY, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev inst4readX : Data.Event := { id := 4, t_id := 1, effect := rOpX, tag := ⟨Normal, Normal.none⟩ }

-- warn: When we define the event, we already defined relation implicitly by giving the value to each event.
-- e.g. We don't know what's the output of a read event unless we know what it reads from.
-- So the assumption for read-from for just e₁ is write and e₂ is write, is weak.

@[simp] abbrev evtsInput : Data.Events := {
  IW := {initWx, initWy}
  R := {inst4readX, inst2readY}
  W := {initWx, initWy, inst1writeX, inst3writeY}
  B := {}
  F := {}
  RMW := {}
}

@[simp] def co : SetRel Event Event := {(initWx, inst1writeX), (initWy, inst3writeY)}

#eval initWx ∈ evtsInput.F

-- Then define co membership decidable
def co_mem_list : List (Event × Event) := [(initWx, inst1writeX), (initWy, inst3writeY)]

instance : wellformed.co evtsInput co where
  irrefl := by aesop
  trans := by aesop
  preco := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

@[simp] def test1 : CandidateExecution evtsInput := {
  evts := evtsInput
  po' := evtsInput.po
  prePo := instWellformedPo evtsInput
  uniqueId := uniqueId_by_id evtsInput
  rf' := {(initWy, inst2readY), (initWx, inst4readX)}
  rfInst := {
    wellTyped := by
      intro w r hrf
      rcases hrf with h | h
      · rcases h with ⟨rfl, rfl⟩; simp
      · rcases h with ⟨rfl, rfl⟩; simp
    unique := by
      intro w₁ w₂ r h1 h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩ <;>
      rcases h2 with ⟨hw2, hr2⟩ | ⟨hw2, hr2⟩ <;>
      subst hw1 hw2 <;>
      first | rfl | exact absurd (hr1 ▸ hr2) (by decide)
  }
  co' := co
  rmw' := ∅
  preRMW := instWellformedRmwEmpty evtsInput
  wmb' := ∅
  mb' := ∅
  data' := ∅
  ctrl' := ∅
  fence' := ∅
  addr' := ∅
  syncInF := by
    intro e h
    contradiction
  rfiPo := by candidateExecution_wf
}

/-- The SB candidate execution has a cycle in `co ∪ rf ∪ fr ∪ po`:
    `inst1writeX →[po] inst2readY →[fr] inst3writeY →[po] inst4readX →[fr] inst1writeX`
    This witnesses that the execution is NOT SC-consistent. -/
theorem FindCycle : ¬ CatRel.SetRel.Acyclic (test1.co' ∪ test1.rf' ∪ test1.fr' ∪ test1.po') := by
  intro h
  apply h inst1writeX
  -- Prove each event is in evtsInput.all (needed for po membership)
  have mem1 : inst1writeX ∈ evtsInput.all := by simp [Events.all]
  have mem2 : inst2readY ∈ evtsInput.all := by simp [Events.all]
  have mem3 : inst3writeY ∈ evtsInput.all := by simp [Events.all]
  have mem4 : inst4readX ∈ evtsInput.all := by simp [Events.all]
  -- Step 1: inst1writeX →[po] inst2readY (same thread P0, id 1 < 2)
  have h1po : (inst1writeX, inst2readY) ∈ test1.po' := by
    have h1evts : (inst1writeX, inst2readY) ∈ evtsInput.po :=
      ⟨mem1, mem2, rfl, by decide⟩
    simpa [test1] using h1evts
  have h1 : (inst1writeX, inst2readY) ∈ test1.co' ∪ test1.rf' ∪ test1.fr' ∪ test1.po' := Or.inr h1po
  -- Step 2: inst2readY →[fr] inst3writeY (via rf⁻¹;co, witness initWy)
  have h2 : (inst2readY, inst3writeY) ∈ test1.co' ∪ test1.rf' ∪ test1.fr' ∪ test1.po' := by
    left; right
    simp only [test1]
    exact ⟨initWy, by simp, by simp [co]⟩
  -- Step 3: inst3writeY →[po] inst4readX (same thread P1, id 3 < 4)
  have h3po : (inst3writeY, inst4readX) ∈ test1.po' := by
    have h3evts : (inst3writeY, inst4readX) ∈ evtsInput.po :=
      ⟨mem3, mem4, rfl, by decide⟩
    simpa [test1] using h3evts
  have h3 : (inst3writeY, inst4readX) ∈ test1.co' ∪ test1.rf' ∪ test1.fr' ∪ test1.po' := Or.inr h3po
  -- Step 4: inst4readX →[fr] inst1writeX (via rf⁻¹;co, witness initWx)
  have h4 : (inst4readX, inst1writeX) ∈ test1.co' ∪ test1.rf' ∪ test1.fr' ∪ test1.po' := by
    left; right
    simp only [test1]
    exact ⟨initWx, by simp, by simp [co]⟩
  exact .head h1 (.head h2 (.head h3 (.single h4)))

-- ════════════════════════════════════════════════════════════════
-- § MP (Message Passing) Litmus Test
-- ════════════════════════════════════════════════════════════════
-- { x=0; y=0; }
--  P0              | P1
--  (1) MOV [x],$1  | (3) MOV EAX,[y]   → reads 1
--  (2) MOV [y],$1  | (4) MOV EBX,[x]   → reads 0
--
-- exists (1:EAX=1 ∧ 1:EBX=0)
--
-- P0 publishes a data write (x) then signals via a flag write (y).
-- P1 sees the signal (y=1) but misses the data (x=0).
-- Forbidden under SC; also forbidden under TSO.
--
-- Cycle: mp_writeX →[po] mp_writeY →[rf] mp_readY →[po] mp_readX →[fr] mp_writeX

-- Use id range 101–111 to avoid clashes with the SB test.
@[simp] abbrev mp_initWx : Data.Event := { id := 110, t_id := 100, effect := initOpX, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev mp_initWy : Data.Event := { id := 111, t_id := 100, effect := initOpY, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev mp_writeX : Data.Event := { id := 101, t_id := 0,   effect := wOpX,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev mp_writeY : Data.Event := { id := 102, t_id := 0,   effect := wOpY,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev mp_readY  : Data.Event := { id := 103, t_id := 1,   effect := rOpY,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev mp_readX  : Data.Event := { id := 104, t_id := 1,   effect := rOpX,    tag := ⟨Normal, Normal.none⟩ }

@[simp] abbrev mp_evts : Data.Events := {
  IW  := {mp_initWx, mp_initWy}
  R   := {mp_readY, mp_readX}
  W   := {mp_initWx, mp_initWy, mp_writeX, mp_writeY}
  B   := {}
  F   := {}
  RMW := {}
}

@[simp] def mp_co : SetRel Event Event := {(mp_initWx, mp_writeX), (mp_initWy, mp_writeY)}

instance : wellformed.co mp_evts mp_co where
  irrefl := by aesop
  trans  := by aesop
  preco  := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

-- rf: mp_readY sees y=1 from mp_writeY; mp_readX sees x=0 from mp_initWx
@[simp] def mp_test : CandidateExecution mp_evts := {
  evts := mp_evts
  po' := mp_evts.po
  prePo := instWellformedPo mp_evts
  uniqueId := uniqueId_by_id mp_evts
  rf'       := {(mp_writeY, mp_readY), (mp_initWx, mp_readX)}
  rfInst   := {
    wellTyped := by
      intro w r hrf
      rcases hrf with h | h
      · rcases h with ⟨rfl, rfl⟩; simp
      · rcases h with ⟨rfl, rfl⟩; simp
    unique := by
      intro w₁ w₂ r h1 h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩ <;>
      rcases h2 with ⟨hw2, hr2⟩ | ⟨hw2, hr2⟩ <;>
      subst hw1 hw2 <;>
      first | rfl | exact absurd (hr1 ▸ hr2) (by decide)
  }
  co'       := mp_co
  rmw'      := ∅
  preRMW := instWellformedRmwEmpty mp_evts
  wmb' := ∅
  mb' := ∅
  data' := ∅
  ctrl' := ∅
  fence' := ∅
  addr' := ∅
  syncInF := by
    intro e h
    contradiction
  rfiPo := by candidateExecution_wf
}

/-- The MP candidate execution has a cycle in `co ∪ rf ∪ fr ∪ po`:
    `mp_writeX →[po] mp_writeY →[rf] mp_readY →[po] mp_readX →[fr] mp_writeX`
    Forbidden under SC. -/
theorem mp_FindCycle : ¬ CatRel.SetRel.Acyclic (mp_test.co' ∪ mp_test.rf' ∪ mp_test.fr' ∪ mp_test.po') := by
  intro h
  apply h mp_writeX
  have mem1 : mp_writeX ∈ mp_evts.all := by simp [Events.all]
  have mem2 : mp_writeY ∈ mp_evts.all := by simp [Events.all]
  have mem3 : mp_readY  ∈ mp_evts.all := by simp [Events.all]
  have mem4 : mp_readX  ∈ mp_evts.all := by simp [Events.all]
  -- Step 1: mp_writeX →[po] mp_writeY (P0, id 101 < 102)
  have h1po : (mp_writeX, mp_writeY) ∈ mp_test.po' := by
    have h1evts : (mp_writeX, mp_writeY) ∈ mp_evts.po :=
      ⟨mem1, mem2, rfl, by decide⟩
    simpa [mp_test] using h1evts
  have h1 : (mp_writeX, mp_writeY) ∈ mp_test.co' ∪ mp_test.rf' ∪ mp_test.fr' ∪ mp_test.po' := Or.inr h1po
  -- Step 2: mp_writeY →[rf] mp_readY
  have h2 : (mp_writeY, mp_readY) ∈ mp_test.co' ∪ mp_test.rf' ∪ mp_test.fr' ∪ mp_test.po' := by
    left; left; right; simp
  -- Step 3: mp_readY →[po] mp_readX (P1, id 103 < 104)
  have h3po : (mp_readY, mp_readX) ∈ mp_test.po' := by
    have h3evts : (mp_readY, mp_readX) ∈ mp_evts.po :=
      ⟨mem3, mem4, rfl, by decide⟩
    simpa [mp_test] using h3evts
  have h3 : (mp_readY, mp_readX) ∈ mp_test.co' ∪ mp_test.rf' ∪ mp_test.fr' ∪ mp_test.po' := Or.inr h3po
  -- Step 4: mp_readX →[fr] mp_writeX (via rf⁻¹;co, witness mp_initWx)
  have h4 : (mp_readX, mp_writeX) ∈ mp_test.co' ∪ mp_test.rf' ∪ mp_test.fr' ∪ mp_test.po' := by
    left; right
    simp only [mp_test]
    exact ⟨mp_initWx, by simp, by simp [mp_co]⟩
  exact .head h1 (.head h2 (.head h3 (.single h4)))

-- ════════════════════════════════════════════════════════════════
-- § LB (Load Buffering) Litmus Test
-- ════════════════════════════════════════════════════════════════
-- { x=0; y=0; }
--  P0              | P1
--  (1) MOV EAX,[x] | (3) MOV EAX,[y]   → reads 1
--  (2) MOV [y],$1  | (4) MOV [x],$1
--
-- exists (0:EAX=1 ∧ 1:EAX=1)
--
-- Each thread reads a location *before* the other thread writes to it,
-- yet both reads see the value 1 — this requires "load buffering" where
-- reads are reordered before writes.
-- Forbidden under SC and TSO; allowed under ARM/POWER.
--
-- Cycle: lb_readX →[po] lb_writeY →[rf] lb_readY →[po] lb_writeX →[rf] lb_readX
-- (note: the cycle uses only po and rf — no fr edges needed)

-- Use id range 201–211 to avoid clashes.
@[simp] abbrev lb_initWx : Data.Event := { id := 210, t_id := 200, effect := initOpX, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev lb_initWy : Data.Event := { id := 211, t_id := 200, effect := initOpY, tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev lb_readX  : Data.Event := { id := 201, t_id := 0,   effect := rOpX,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev lb_writeY : Data.Event := { id := 202, t_id := 0,   effect := wOpY,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev lb_readY  : Data.Event := { id := 203, t_id := 1,   effect := rOpY,    tag := ⟨Normal, Normal.none⟩ }
@[simp] abbrev lb_writeX : Data.Event := { id := 204, t_id := 1,   effect := wOpX,    tag := ⟨Normal, Normal.none⟩ }

@[simp] abbrev lb_evts : Data.Events := {
  IW  := {lb_initWx, lb_initWy}
  R   := {lb_readX, lb_readY}
  W   := {lb_initWx, lb_initWy, lb_writeY, lb_writeX}
  B   := {}
  F   := {}
  RMW := {}
}

@[simp] def lb_co : SetRel Event Event := {(lb_initWx, lb_writeX), (lb_initWy, lb_writeY)}

instance : wellformed.co lb_evts lb_co where
  irrefl := by aesop
  trans  := by aesop
  preco  := {
    wellTyped := by aesop
    total := by candidateExecution_wf
  }

-- rf: lb_readX sees x=1 from lb_writeX; lb_readY sees y=1 from lb_writeY
@[simp] def lb_test : CandidateExecution lb_evts := {
  evts := lb_evts
  po' := lb_evts.po
  prePo := instWellformedPo lb_evts
  uniqueId := uniqueId_by_id lb_evts
  rf'       := {(lb_writeX, lb_readX), (lb_writeY, lb_readY)}
  rfInst   := {
    wellTyped := by
      intro w r hrf
      rcases hrf with h | h
      · rcases h with ⟨rfl, rfl⟩; simp
      · rcases h with ⟨rfl, rfl⟩; simp
    unique := by
      intro w₁ w₂ r h1 h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩ <;>
      rcases h2 with ⟨hw2, hr2⟩ | ⟨hw2, hr2⟩ <;>
      subst hw1 hw2 <;>
      first | rfl | exact absurd (hr1 ▸ hr2) (by decide)
  }
  co'       := lb_co
  rmw'      := ∅
  preRMW := instWellformedRmwEmpty lb_evts
  wmb' := ∅
  mb' := ∅
  data' := ∅
  ctrl' := ∅
  fence' := ∅
  addr' := ∅
  syncInF := by
    intro e h
    contradiction
  rfiPo := by candidateExecution_wf
}

/-- The LB candidate execution has a cycle in `co ∪ rf ∪ fr ∪ po`:
    `lb_readX →[po] lb_writeY →[rf] lb_readY →[po] lb_writeX →[rf] lb_readX`
    The cycle uses only `po` and `rf` — no `fr` edges are needed.
    Forbidden under SC and TSO; allowed under ARM/POWER. -/
theorem lb_FindCycle : ¬ CatRel.SetRel.Acyclic (lb_test.co' ∪ lb_test.rf' ∪ lb_test.fr' ∪ lb_test.po') := by
  intro h
  apply h lb_readX
  have mem1 : lb_readX  ∈ lb_evts.all := by simp [Events.all]
  have mem2 : lb_writeY ∈ lb_evts.all := by simp [Events.all]
  have mem3 : lb_readY  ∈ lb_evts.all := by simp [Events.all]
  have mem4 : lb_writeX ∈ lb_evts.all := by simp [Events.all]
  -- Step 1: lb_readX →[po] lb_writeY (P0, id 201 < 202)
  have h1po : (lb_readX, lb_writeY) ∈ lb_test.po' := by
    have h1evts : (lb_readX, lb_writeY) ∈ lb_evts.po :=
      ⟨mem1, mem2, rfl, by decide⟩
    simpa [lb_test] using h1evts
  have h1 : (lb_readX, lb_writeY) ∈ lb_test.co' ∪ lb_test.rf' ∪ lb_test.fr' ∪ lb_test.po' := Or.inr h1po
  -- Step 2: lb_writeY →[rf] lb_readY
  have h2 : (lb_writeY, lb_readY) ∈ lb_test.co' ∪ lb_test.rf' ∪ lb_test.fr' ∪ lb_test.po' := by
    left; left; right; simp
  -- Step 3: lb_readY →[po] lb_writeX (P1, id 203 < 204)
  have h3po : (lb_readY, lb_writeX) ∈ lb_test.po' := by
    have h3evts : (lb_readY, lb_writeX) ∈ lb_evts.po :=
      ⟨mem3, mem4, rfl, by decide⟩
    simpa [lb_test] using h3evts
  have h3 : (lb_readY, lb_writeX) ∈ lb_test.co' ∪ lb_test.rf' ∪ lb_test.fr' ∪ lb_test.po' := Or.inr h3po
  -- Step 4: lb_writeX →[rf] lb_readX
  have h4 : (lb_writeX, lb_readX) ∈ lb_test.co' ∪ lb_test.rf' ∪ lb_test.fr' ∪ lb_test.po' := by
    left; left; right; simp
  exact .head h1 (.head h2 (.head h3 (.single h4)))

end Litmus
