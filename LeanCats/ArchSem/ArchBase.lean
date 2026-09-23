import LeanCats.Basic

namespace ArchBase
open Data

structure Spec {evts : Events} (X : CandidateExecution evts) where
  -- fences are binary relations that between two events.
  fences : Array Event
  branches : Array $ Event
  barriers : Array $ SetRel Event Event

end ArchBase
