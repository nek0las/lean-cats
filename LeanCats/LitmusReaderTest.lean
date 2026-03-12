/-
  LitmusReaderTest.lean — Test the litmus file reader commands.
-/
import LeanCats.LitmusReader
import LeanCats.LitmusGraph
import LeanCats.LitmusGraphBridge

-- Classic 2-thread tests
#litmus "LeanCats/examples/tests/SB.litmus"
#litmus "LeanCats/examples/tests/MP.litmus"
#litmus "LeanCats/examples/tests/LB.litmus"
#litmus "LeanCats/examples/tests/CoWW.litmus"
#litmus "LeanCats/examples/tests/CoWR.litmus"
#litmus "LeanCats/examples/tests/CoRW.litmus"
#litmus "LeanCats/examples/tests/CoRR.litmus"
#litmus "LeanCats/examples/tests/WRR.litmus"
#litmus "LeanCats/examples/tests/RRW.litmus"
#litmus "LeanCats/examples/tests/WWC.litmus"
#litmus "LeanCats/examples/tests/WRW.litmus"
#litmus "LeanCats/examples/tests/2W.litmus"

deflitmus SB <"LeanCats/examples/tests/SB.litmus">

def a := LitmusGraphBridge.candExecToConcreteExec SB[0]!
#html LitmusGraph.toOrderedHtml a

-- With MFENCE
#litmus "LeanCats/examples/tests/SB_MFence.litmus"
#litmus "LeanCats/examples/tests/MP_MFence.litmus"
#litmus "LeanCats/examples/tests/LB_MFence.litmus"

-- 3-thread tests
#litmus "LeanCats/examples/tests/WRC.litmus"
#litmus "LeanCats/examples/tests/RWC.litmus"
#litmus "LeanCats/examples/tests/ISA2.litmus"
#litmus "LeanCats/examples/tests/3SB.litmus"
#litmus "LeanCats/examples/tests/3LB.litmus"
#litmus "LeanCats/examples/tests/3MP.litmus"
#litmus "LeanCats/examples/tests/RWC_MFence.litmus"
#litmus "LeanCats/examples/tests/ISA2_MFence.litmus"
#litmus "LeanCats/examples/tests/MP2.litmus"
#litmus "LeanCats/examples/tests/SB_opt.litmus"
#litmus "LeanCats/examples/tests/3SB_MFence.litmus"

-- 4-thread tests
#litmus "LeanCats/examples/tests/IRIW.litmus"
#litmus "LeanCats/examples/tests/IRIW_MFence.litmus"
#litmus "LeanCats/examples/tests/4SB.litmus"
#litmus "LeanCats/examples/tests/4LB.litmus"
