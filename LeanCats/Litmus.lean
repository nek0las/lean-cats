-- In this file, we define a serias of instructions to prove if it's allowed or not regarding to a specific model.
import LeanCats.Basic
import LeanCats.Data
open Data
namespace Litmus
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
  M := {}
}

@[simp] def co : SetRel Event Event := {(initWx, inst1writeX), (initWy, inst3writeY)}

#eval initWx ∈ evtsInput.F

-- Then define co membership decidable
def co_mem_list : List (Event × Event) := [(initWx, inst1writeX), (initWy, inst3writeY)]

instance : wellformed.co evtsInput co where
  irrefl := by aesop
  trans := by aesop
  preco := by aesop

@[simp] def test1 : CandidateExecution evtsInput := {
  uniqueId := by aesop
  rf := {(initWy, inst2readY), (initWx, inst4readX)}
  rfInst := by aesop
  co := co
  rmw := ∅
}

/-- The SB candidate execution has a cycle in `co ∪ rf ∪ fr ∪ po`:
    `inst1writeX →[po] inst2readY →[fr] inst3writeY →[po] inst4readX →[fr] inst1writeX`
    This witnesses that the execution is NOT SC-consistent. -/
theorem FindCycle : ¬ CatRel.Acyclic (test1.co ∪ test1.rf ∪ test1.fr ∪ test1.po) := by
  intro h
  apply h inst1writeX
  -- Prove each event is in evtsInput.all (needed for po membership)
  have mem1 : inst1writeX ∈ evtsInput.all := by simp [Events.all]
  have mem2 : inst2readY ∈ evtsInput.all := by simp [Events.all]
  have mem3 : inst3writeY ∈ evtsInput.all := by simp [Events.all]
  have mem4 : inst4readX ∈ evtsInput.all := by simp [Events.all]
  -- Step 1: inst1writeX →[po] inst2readY (same thread P0, id 1 < 2)
  have h1 : (inst1writeX, inst2readY) ∈ test1.co ∪ test1.rf ∪ test1.fr ∪ test1.po :=
    Or.inr ⟨mem1, mem2, rfl, by decide⟩
  -- Step 2: inst2readY →[fr] inst3writeY (via rf⁻¹;co, witness initWy)
  have h2 : (inst2readY, inst3writeY) ∈ test1.co ∪ test1.rf ∪ test1.fr ∪ test1.po := by
    left; right
    simp only [test1, SetRel.mem_comp, SetRel.mem_inv]
    exact ⟨initWy, by simp, by simp [co]⟩
  -- Step 3: inst3writeY →[po] inst4readX (same thread P1, id 3 < 4)
  have h3 : (inst3writeY, inst4readX) ∈ test1.co ∪ test1.rf ∪ test1.fr ∪ test1.po :=
    Or.inr ⟨mem3, mem4, rfl, by decide⟩
  -- Step 4: inst4readX →[fr] inst1writeX (via rf⁻¹;co, witness initWx)
  have h4 : (inst4readX, inst1writeX) ∈ test1.co ∪ test1.rf ∪ test1.fr ∪ test1.po := by
    left; right
    simp only [test1, SetRel.mem_comp, SetRel.mem_inv]
    exact ⟨initWx, by simp, by simp [co]⟩
  exact .head h1 (.head h2 (.head h3 (.single h4)))

end Litmus
