import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

open CatRel Data

/--
Partial result: the currently formalized BPF-vs-LKMM comparison only covers the
coherence axiom. The fence-dependent hb/propagation arguments are still
unfinished, so this file keeps only the fragment that is fully proved.
-/
theorem bpfStrongerThanLKMM
  (evts : Data.Events)
  (X : CandidateExecution evts)
  : bpf.Coherence evts X → lkmm.coherence evts X := by
  intro hcoh
  simpa [bpf.Coherence, lkmm.coherence, bpf.com, lkmm.com,
      CatRel.CatUnion.union, or_left_comm, or_assoc, or_comm,
      Set.mem_setOf_eq] using hcoh
