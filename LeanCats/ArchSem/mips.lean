import LeanCats.Basic

-- This is one example on how to define a architecture-specific instruction.
-- Architecture-specific event classes used by MIPS CAT models.
namespace mips
open Data

def SYNC (evts : Events) (X : CandidateExecution evts) : Set Event := { e | e ∈ X.evts.F }

end mips
