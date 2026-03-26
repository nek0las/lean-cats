/-
  LitmusParser/Types.lean — Architecture-independent types for candidate executions.
-/
import LeanCats.Data

open Data

namespace LitmusParser

-- ════════════════════════════════════════════════════════════════
-- Exists Constraint (shared across all architectures)
-- ════════════════════════════════════════════════════════════════

/-- One conjunct in the exists clause: thread `tid`, register `reg` has value `val`. -/
structure ExistsConjunct where
  tid : Nat
  reg : String
  val : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The `exists (...)` constraint: a conjunction of register-value assertions. -/
structure ExistsConstraint where
  conjuncts : Array ExistsConjunct
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════
-- Concrete Event & Candidate Execution
-- ════════════════════════════════════════════════════════════════

/-- A concrete event with all fields computable. -/
structure CEvent where
  id     : Nat
  t_id   : Nat
  op     : Op
  loc    : Nat            -- location index (mapped from name)
  locName: String := ""   -- original name for display
  val    : Option Nat     -- value written, or value read (once rf is chosen)
  isInit : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString CEvent where
  toString e :=
    let opStr := if e.op == .write then (if e.isInit then "IW" else "W")
      else if e.op == .read then "R"
      else if e.op == .fence then "F"
      else "B"
    let valStr := match e.val with | some v => s!"={v}" | none => ""
    s!"{opStr}({e.locName}{valStr})[id={e.id},tid={e.t_id}]"

instance : Hashable CEvent where
  hash e := hash e.id

/-- A concrete candidate execution with array-based computable relations. -/
structure ConcreteCandExec where
  allEvents  : Array CEvent
  initWrites : Array CEvent
  reads      : Array CEvent
  writes     : Array CEvent       -- program writes only (not init)
  po         : Array (Nat × Nat)  -- (from_id, to_id)
  rf         : Array (Nat × Nat)  -- (write_id, read_id)
  co         : Array (Nat × Nat)  -- (earlier_write_id, later_write_id)
  fr         : Array (Nat × Nat)  -- derived: rf⁻¹ ; co
  deriving Repr, Inhabited

instance : ToString ConcreteCandExec where
  toString e :=
    let fmtRel (name : String) (rel : Array (Nat × Nat)) : String :=
      let pairs := rel.toList.map fun (a, b) => s!"({a},{b})"
      s!"{name}: [{", ".intercalate pairs}]"
    let eventStrs := e.allEvents.toList.map toString
    s!"Events: [{", ".intercalate eventStrs}]\n" ++
    fmtRel "po" e.po ++ "\n" ++
    fmtRel "rf" e.rf ++ "\n" ++
    fmtRel "co" e.co ++ "\n" ++
    fmtRel "fr" e.fr

-- ════════════════════════════════════════════════════════════════
-- Generated Events (output of architecture-specific event generation)
-- ════════════════════════════════════════════════════════════════

/-- Result of generating events from a parsed litmus test.
    Each architecture produces this as input to the generic enumeration. -/
structure GeneratedEvents where
  allEvents  : Array CEvent
  initWrites : Array CEvent
  reads      : Array CEvent
  progWrites : Array CEvent
  fences     : Array CEvent
  po         : Array (Nat × Nat)
  locs       : Array String
  initVals   : Array Nat
  /-- For each read event: (event_id, register_name, thread_id). -/
  readRegs   : Array (Nat × String × Nat)
  deriving Repr, Inhabited

end LitmusParser
