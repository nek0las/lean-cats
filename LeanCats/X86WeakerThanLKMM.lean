import LeanCats.Macro
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

/-- x86/TSO is weaker than LKMM: any execution consistent under x86/TSO is also
    consistent under LKMM. x86 operations are plain R/W with no LKMM access-type
    annotations, so the annotation-dependent LKMM constraints (happens_before,
    propagation) are vacuously satisfied, and coherence is the meaningful obligation. -/
theorem tso_x86_subset_lkmm
    (evts : Data.Events)
    (X : CandidateExecution evts)
    (hTso : tso_x86.tso evts X) :
    lkmm.coherence evts X ∧
    lkmm.atomic evts X ∧
    lkmm.happens_before evts X ∧
    lkmm.propagation evts X := by
  sorry
