/-
  LitmusParserTest.lean — Programmatically test that the litmus parser can parse
  all 30 litmus test files in LeanCats/examples/tests/.
-/
import LeanCats.LitmusParser

open LitmusParser LitmusParser.X86

def testDir : String := "LeanCats/examples/tests"

def allLitmusFiles : Array String := #[
  "2W.litmus",
  "3LB.litmus",
  "3MP.litmus",
  "3SB.litmus",
  "3SB_MFence.litmus",
  "4LB.litmus",
  "4SB.litmus",
  "CoRR.litmus",
  "CoRW.litmus",
  "CoWR.litmus",
  "CoWW.litmus",
  "IRIW.litmus",
  "IRIW_MFence.litmus",
  "ISA2.litmus",
  "ISA2_MFence.litmus",
  "LB.litmus",
  "LB_MFence.litmus",
  "MP.litmus",
  "MP2.litmus",
  "MP_MFence.litmus",
  "RRW.litmus",
  "RWC.litmus",
  "RWC_MFence.litmus",
  "SB.litmus",
  "SB_MFence.litmus",
  "SB_opt.litmus",
  "WRC.litmus",
  "WRR.litmus",
  "WRW.litmus",
  "WWC.litmus"
]

/-- Run parse+enumerate on every file; return (passed, failed) counts + failure list. -/
def runAllTests : IO (Nat × Nat × Array String) := do
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut failures : Array String := #[]
  for fname in allLitmusFiles do
    let path := testDir ++ "/" ++ fname
    let contents ← IO.FS.readFile path
    match parseLitmusAndEnumerate contents with
    | .ok execs =>
      passed := passed + 1
      IO.println s!"  PASS  {fname} ({execs.size} candidate(s))"
    | .error e =>
      failed := failed + 1
      failures := failures.push fname
      IO.println s!"  FAIL  {fname} — {e}"
  return (passed, failed, failures)

def main : IO Unit := do
  IO.println "════════════════════════════════════════════════════"
  IO.println "  X86 Litmus Parser — Test Suite"
  IO.println s!"  Directory: {testDir}"
  IO.println s!"  Files:     {allLitmusFiles.size}"
  IO.println "════════════════════════════════════════════════════"
  let (passed, failed, failures) ← runAllTests
  IO.println "────────────────────────────────────────────────────"
  IO.println s!"  Results:  {passed} passed,  {failed} failed"
  if failures.isEmpty then
    IO.println "  ✓ All tests passed."
  else
    IO.println "  ✗ Failures:"
    for f in failures do
      IO.println s!"      {f}"
  IO.println "════════════════════════════════════════════════════"
  if failed > 0 then
    IO.Process.exit 1

#eval main
