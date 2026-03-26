/-
  LitmusParser/Enumeration.lean — Architecture-independent RF / CO / FR enumeration
  and candidate execution assembly.

  All functions here operate on `GeneratedEvents` and `ExistsConstraint`,
  which are produced by architecture-specific event generators.
-/
import LeanCats.LitmusParser.Types

namespace LitmusParser

-- ════════════════════════════════════════════════════════════════
-- Combinatorial Helpers
-- ════════════════════════════════════════════════════════════════

/-- Cartesian product of arrays of choices. -/
private def cartesianProduct (choices : Array (Array α)) : Array (Array α) := Id.run do
  let mut result : Array (Array α) := #[#[]]
  for opts in choices do
    let mut newResult : Array (Array α) := #[]
    for partial_ in result do
      for opt in opts do
        newResult := newResult.push (partial_.push opt)
    result := newResult
  return result

/-- Generate all permutations of a list. (partial since termination proof is nontrivial) -/
private partial def permutations [DecidableEq α] : List α → List (List α)
  | [] => [[]]
  | xs => xs.flatMap fun x =>
      (permutations (xs.erase x)).map (x :: ·)

/-- Convert a total order (array of write-ids) into co pairs: (earlier, later). -/
private def orderToPairs (order : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut pairs : Array (Nat × Nat) := #[]
  for i in [:order.size] do
    for j in [i+1:order.size] do
      pairs := pairs.push (order[i]!, order[j]!)
  return pairs

-- ════════════════════════════════════════════════════════════════
-- RF Enumeration
-- ════════════════════════════════════════════════════════════════

/-- For each read event, find all writes (init + program) to the same location. -/
def rfChoicesPerRead (gen : GeneratedEvents) : Array (Array Nat) := Id.run do
  let allWrites := gen.initWrites ++ gen.progWrites
  let mut choices : Array (Array Nat) := #[]
  for r in gen.reads do
    let mut writesForLoc : Array Nat := #[]
    for w in allWrites do
      if w.loc == r.loc && w.id != r.id then writesForLoc := writesForLoc.push w.id
    choices := choices.push writesForLoc
  return choices

/-- Enumerate all possible rf assignments. `result[i]` = write-id that reads[i] reads from. -/
def enumerateRfAssignments (gen : GeneratedEvents) : Array (Array Nat) :=
  cartesianProduct (rfChoicesPerRead gen)

/-- Given an rf assignment, determine the value each read sees. -/
def rfToReadValues (gen : GeneratedEvents) (rfAssign : Array Nat) : Array (Nat × Nat) := Id.run do
  let allWrites := gen.initWrites ++ gen.progWrites
  let mut result : Array (Nat × Nat) := #[]
  for i in [:gen.reads.size] do
    let writeId := rfAssign[i]!
    let mut writeVal : Nat := 0
    for w in allWrites do
      if w.id == writeId then
        writeVal := w.val.getD 0
        break
    result := result.push (gen.reads[i]!.id, writeVal)
  return result

/-- Check whether an rf assignment satisfies the `exists` constraint. -/
def checkConstraint (gen : GeneratedEvents) (rfAssign : Array Nat)
    (constraint : ExistsConstraint) : Bool := Id.run do
  let readVals := rfToReadValues gen rfAssign
  for conj in constraint.conjuncts do
    let mut lastReadVal : Option Nat := none
    for (readId, reg, tid) in gen.readRegs do
      if tid == conj.tid && reg == conj.reg then
        for (rid, val) in readVals do
          if rid == readId then
            lastReadVal := some val
            break
    match lastReadVal with
    | some v => if v != conj.val then return false
    | none   => return false
  return true

-- ════════════════════════════════════════════════════════════════
-- CO Enumeration
-- ════════════════════════════════════════════════════════════════

/-- For each location, enumerate all total orders on its writes (init first). -/
def coOrdersPerLocation (gen : GeneratedEvents) : Array (Array (Array Nat)) := Id.run do
  let mut result : Array (Array (Array Nat)) := #[]
  for locIdx in [:gen.locs.size] do
    let initW := gen.initWrites.filter (·.loc == locIdx) |>.map (·.id)
    let progW := gen.progWrites.filter (·.loc == locIdx) |>.map (·.id)
    let perms := permutations progW.toList
    let mut orders : Array (Array Nat) := #[]
    for perm in perms do
      orders := orders.push (initW ++ perm.toArray)
    if orders.isEmpty then orders := #[initW]
    result := result.push orders
  return result

/-- Compute fr = rf⁻¹ ; co. -/
def computeFr (rf : Array (Nat × Nat)) (co : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut fr : Array (Nat × Nat) := #[]
  for (w, r) in rf do
    for (w1, w2) in co do
      if w == w1 then fr := fr.push (r, w2)
  return fr

-- ════════════════════════════════════════════════════════════════
-- Candidate Execution Assembly
-- ════════════════════════════════════════════════════════════════

/-- Enumerate all candidate executions.
    Architecture-independent: takes `GeneratedEvents` produced by any arch-specific generator. -/
def enumerateCandidateExecutions (gen : GeneratedEvents) : Array ConcreteCandExec := Id.run do
  let rfAssignments := enumerateRfAssignments gen
  let coPerLoc := coOrdersPerLocation gen
  let coChoices := cartesianProduct coPerLoc

  let mut results : Array ConcreteCandExec := #[]

  for rfAssign in rfAssignments do
    let mut rfEdges : Array (Nat × Nat) := #[]
    for i in [:gen.reads.size] do
      rfEdges := rfEdges.push (rfAssign[i]!, gen.reads[i]!.id)

    for coChoice in coChoices do
      let mut coEdges : Array (Nat × Nat) := #[]
      for locOrder in coChoice do
        coEdges := coEdges ++ orderToPairs locOrder
      let frEdges := computeFr rfEdges coEdges

      -- Annotate read events with the values they see from rf
      let readVals := rfToReadValues gen rfAssign
      let mut updatedEvents := gen.allEvents
      for (rid, rval) in readVals do
        for j in [:updatedEvents.size] do
          if updatedEvents[j]!.id == rid then
            updatedEvents := updatedEvents.set! j { updatedEvents[j]! with val := some rval }

      let exec : ConcreteCandExec := {
        allEvents := updatedEvents, initWrites := gen.initWrites,
        reads := gen.reads, writes := gen.progWrites,
        po := gen.po, rf := rfEdges, co := coEdges, fr := frEdges
      }
      results := results.push exec
  return results

/-- Enumerate candidate executions that satisfy the `exists` constraint. -/
def enumerateConstrainedCandidateExecutions (gen : GeneratedEvents) (constraint : ExistsConstraint)
    : Array ConcreteCandExec :=
  (enumerateCandidateExecutions gen).filter fun exec =>
    let rfAssign := gen.reads.map fun r =>
      match exec.rf.find? (fun (_, rid) => rid == r.id) with
      | some (wid, _) => wid
      | none => 0
    checkConstraint gen rfAssign constraint

end LitmusParser
