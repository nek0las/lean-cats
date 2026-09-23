import LeanCats.Basic
import LeanCats.ArchSem.ArchBase

-- Architecture-specific event classes used by MIPS CAT models.
namespace MIPS
open Data

structure Spec {evts : Events} (X : CandidateExecution evts) extends ArchBase.Spec X  where
  SYNC := { e | e ∈ evts.F }

end MIPS
