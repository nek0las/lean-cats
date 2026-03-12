/-
  LitmusParser/X86.lean — X86-specific litmus test parsing and event generation.

  Other architectures (e.g., ARM, RISC-V) can follow the same pattern:
  1. Define an instruction type.
  2. Implement instruction parsing.
  3. Implement `generateEvents` producing `GeneratedEvents`.
  4. Call the shared `enumerateCandidateExecutions`.
-/
import LeanCats.LitmusParser.Helpers
import LeanCats.LitmusParser.Enumeration

open Data

namespace LitmusParser.X86

-- ════════════════════════════════════════════════════════════════
-- X86 Instruction Set & Parsed Litmus Test
-- ════════════════════════════════════════════════════════════════

/-- A single x86 instruction from a litmus test. -/
inductive LitmusInst where
  | store (loc : String) (val : Nat)        -- MOV [loc],$val
  | load  (reg : String) (loc : String)     -- MOV reg,[loc]
  | fence                                   -- MFENCE
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A fully parsed X86 litmus test. -/
structure ParsedLitmus where
  arch       : String := "X86"
  name       : String := ""
  initState  : Array (String × Nat)      -- (location_name, initial_value)
  threads    : Array (Array LitmusInst)   -- threads[tid][program_order_index]
  constraint : ExistsConstraint
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════
-- X86 Instruction Parser
-- ════════════════════════════════════════════════════════════════

/-- Parse one x86 instruction string like `MOV [x],$1` or `MOV EAX,[y]` or `MFENCE`. -/
def parseOneInst (s : String) : Option LitmusInst := Id.run do
  let s := strim s
  if s.isEmpty then return none

  -- MFENCE
  if s.toUpper == "MFENCE" then return some .fence

  -- Must start with MOV (case-insensitive)
  let tokens := s.splitOn " " |>.filter (strim · != "")
  if tokens.length < 2 then return none
  let mnemonic := tokens[0]!.toUpper
  -- Rejoin the rest so we can split on ','
  let rest := ",".intercalate (tokens.drop 1)
  let operands := rest.splitOn ","
  if mnemonic != "MOV" || operands.length < 2 then return none

  let op1 := strim operands[0]!  -- destination
  let op2 := strim operands[1]!  -- source

  -- Store: MOV [loc],$val
  if op1.startsWith "[" then
    let locName := strim (sdropSuffix (sdropPrefix op1 "[") "]")
    let valStr := strim (sdropPrefix op2 "$")
    if let some val := parseNat valStr then
      return some (.store locName val)
    return none

  -- Load: MOV reg,[loc]
  if op2.startsWith "[" then
    let locName := strim (sdropSuffix (sdropPrefix op2 "[") "]")
    return some (.load op1 locName)

  return none

-- ════════════════════════════════════════════════════════════════
-- X86 Thread Program Parser
-- ════════════════════════════════════════════════════════════════

/-- Parse thread instruction columns from the program lines. -/
def parseThreadPrograms (lines : Array String) : Array (Array LitmusInst) := Id.run do
  if lines.isEmpty then return #[]
  let firstLine := lines[0]!
  let cols := firstLine.splitOn "|"
  let numThreads := cols.length
  let mut threads : Array (Array LitmusInst) := #[]
  for _ in [:numThreads] do threads := threads.push #[]

  for i in [1:lines.size] do
    let line := strim (sdropSuffix (strim lines[i]!) ";")
    if line.isEmpty then continue
    let cols := line.splitOn "|"
    for tid in [:numThreads] do
      if tid < cols.length then
        let instStr := strim cols[tid]!
        if let some inst := parseOneInst instStr then
          threads := threads.set! tid (threads[tid]!.push inst)
  return threads

-- ════════════════════════════════════════════════════════════════
-- X86 Main Parser
-- ════════════════════════════════════════════════════════════════

/-- Parse a complete X86 litmus test string into `ParsedLitmus`. -/
def parseLitmus (input : String) : Except String ParsedLitmus := do
  let lines := (input.splitOn "\n" |>.map strim |>.filter (· != "")).toArray
  if lines.size < 3 then
    throw "Litmus test too short"

  -- Line 0: architecture and test name
  let headerTokens := lines[0]!.splitOn " " |>.filter (· != "")
  let arch := if headerTokens.length > 0 then headerTokens[0]! else "X86"
  let name := if headerTokens.length > 1 then headerTokens[1]! else ""

  -- Find lines containing '{' (initial state) and 'exists' (constraint)
  let mut initState : Array (String × Nat) := #[]
  let mut initLineIdx : Nat := 0
  let mut constraint : ExistsConstraint := { conjuncts := #[] }
  let mut existsLineIdx : Nat := lines.size

  for i in [:lines.size] do
    if scontains lines[i]! "{" then
      initState := parseInitState lines[i]!
      initLineIdx := i
    if lines[i]!.toLower.startsWith "exists" then
      constraint := parseExists lines[i]!
      existsLineIdx := i

  -- Everything between initState and exists is the program
  let mut programLines : Array String := #[]
  for i in [initLineIdx + 1 : existsLineIdx] do
    let l := lines[i]!
    if !l.startsWith "\"" then
      programLines := programLines.push l

  let threads := parseThreadPrograms programLines

  return {
    arch
    name
    initState
    threads
    constraint
  }

-- ════════════════════════════════════════════════════════════════
-- X86 Event Generation
-- ════════════════════════════════════════════════════════════════

/-- Map location names to Nat indices for an X86 litmus test. -/
def buildLocMap (initState : Array (String × Nat)) (threads : Array (Array LitmusInst))
    : Array String := Id.run do
  let mut locs : Array String := #[]
  for (loc, _) in initState do
    if !locs.contains loc then locs := locs.push loc
  for thread in threads do
    for inst in thread do
      let loc := match inst with
        | .store l _ => l
        | .load _ l  => l
        | .fence     => ""
      if loc != "" && !locs.contains loc then locs := locs.push loc
  return locs

/-- Generate events and program-order edges from a parsed X86 litmus test. -/
def generateEvents (test : ParsedLitmus) : GeneratedEvents := Id.run do
  let locs := buildLocMap test.initState test.threads
  let mut initVals : Array Nat := #[]
  for _ in [:locs.size] do initVals := initVals.push 0
  for (loc, val) in test.initState do
    let idx := locIndex locs loc
    if idx < initVals.size then initVals := initVals.set! idx val

  let initIdBase := 1000
  let mut allEvents : Array CEvent := #[]
  let mut initWrites : Array CEvent := #[]

  -- Create initial write events (one per location)
  for i in [:locs.size] do
    let ev : CEvent := {
      id := initIdBase + i, t_id := initIdBase, op := .write,
      loc := i, locName := locs[i]!, val := some initVals[i]!, isInit := true
    }
    allEvents := allEvents.push ev
    initWrites := initWrites.push ev

  -- Create instruction events
  let mut reads : Array CEvent := #[]
  let mut progWrites : Array CEvent := #[]
  let mut fences : Array CEvent := #[]
  let mut po : Array (Nat × Nat) := #[]
  let mut readRegs : Array (Nat × String × Nat) := #[]
  let mut nextId : Nat := 1

  for tid in [:test.threads.size] do
    let thread := test.threads[tid]!
    let mut prevId : Option Nat := none
    for inst in thread do
      let evId := nextId
      nextId := nextId + 1
      let ev : CEvent := match inst with
        | .store loc val =>
          let li := locIndex locs loc
          { id := evId, t_id := tid, op := .write, loc := li,
            locName := loc, val := some val, isInit := false }
        | .load _reg loc =>
          let li := locIndex locs loc
          { id := evId, t_id := tid, op := .read, loc := li,
            locName := loc, val := none, isInit := false }
        | .fence =>
          { id := evId, t_id := tid, op := .fence, loc := 0,
            locName := "", val := none, isInit := false }

      allEvents := allEvents.push ev
      match inst with
      | .store _ _ => progWrites := progWrites.push ev
      | .load reg _ =>
        reads := reads.push ev
        readRegs := readRegs.push (evId, reg, tid)
      | .fence => fences := fences.push ev

      if let some prev := prevId then po := po.push (prev, evId)
      prevId := some evId

  return { allEvents, initWrites, reads, progWrites, fences, po, locs, initVals, readRegs }

-- ════════════════════════════════════════════════════════════════
-- X86 Convenience API
-- ════════════════════════════════════════════════════════════════

/-- Parse an X86 litmus test string and enumerate all candidate executions. -/
def parseLitmusAndEnumerate (input : String) : Except String (Array ConcreteCandExec) := do
  let test ← parseLitmus input
  let gen := generateEvents test
  return enumerateCandidateExecutions gen test.constraint

-- ════════════════════════════════════════════════════════════════
-- Example X86 Litmus Test Strings
-- ════════════════════════════════════════════════════════════════

def sbLitmusStr : String :=
"X86 SB
{ x=0; y=0; }
P0          | P1          ;
MOV [x],$1  | MOV [y],$1  ;
MOV EAX,[y] | MOV EAX,[x] ;
exists (0:EAX=0 /\\ 1:EAX=0)"

def mpLitmusStr : String :=
"X86 MP
{ x=0; y=0; }
P0          | P1          ;
MOV [x],$1  | MOV EAX,[y] ;
MOV [y],$1  | MOV EBX,[x] ;
exists (1:EAX=1 /\\ 1:EBX=0)"

def lbLitmusStr : String :=
"X86 LB
{ x=0; y=0; }
P0          | P1          ;
MOV EAX,[x] | MOV EAX,[y] ;
MOV [y],$1  | MOV [x],$1  ;
exists (0:EAX=1 /\\ 1:EAX=1)"

-- ════════════════════════════════════════════════════════════════
-- Computable Tests
-- ════════════════════════════════════════════════════════════════

/-- Helper: format one litmus result set. -/
def reportResults (label : String) (input : String) : String :=
  match parseLitmusAndEnumerate input with
  | .ok results =>
    let header := s!"{label}: {results.size} candidate execution(s) matching constraint\n"
    results.foldl (fun acc r => acc ++ s!"---\n{r}\n") header
  | .error e => s!"Error: {e}"

#eval! reportResults "SB" sbLitmusStr
#eval! reportResults "MP" mpLitmusStr
#eval! reportResults "LB" lbLitmusStr

end LitmusParser.X86
