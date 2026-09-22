import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic
import LeanCats.mipsWeakerThanTSO

-- `sc.cat` intentionally defines `sc.sc`: the file name names the model namespace
-- and the model itself names its consistency predicate.
set_option linter.dupNamespace false in
defcat <"sc.cat">

theorem scvtso
  (evts : Data.Events)
  (X : CandidateExecution evts)
  : sc.sc evts X → tsox.tso evts X :=
by
  unfold sc.sc
  simp
  intro sc
  apply ayclicMono sc
  simp [CatRel.CatUnion.union] at *
  intro a b h
  rcases h with hImplied | h
  · rcases hImplied with ⟨mid, hpo, hId⟩ | ⟨mid, hId, hpo⟩
    · rcases hId with ⟨rfl, _⟩
      exact Or.inl hpo
    · rcases hId with ⟨rfl, _⟩
      exact Or.inl hpo
  · rcases h with hxppo | h
    · exact Or.inl hxppo.2
    · rcases h with hrfe | h
      · exact Or.inr (Or.inl hrfe.1)
      · rcases h with hfr | hco
        · exact Or.inr (Or.inr (Or.inl hfr))
        · exact Or.inr (Or.inr (Or.inr hco))
