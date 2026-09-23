import LeanCats.CatParser.Macro
import LeanCats.CatParser.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic
import LeanCats.Examples.mipsWeakerThanTSO

defcat <"bpf.cat">

theorem scvtso
  (evts : Data.Events)
  (X : CandidateExecution evts)
  : sc.sc evts X → tsox.tso evts X :=
