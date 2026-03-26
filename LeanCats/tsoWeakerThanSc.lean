import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

defcat <"tso.cat">
defcat <"sc.cat">

theorem scvtso
  (evts : Data.Events)
  (X : CandidateExecution evts)
  : sc.sc evts X → tso.tso evts X :=
by
  unfold sc.sc
  simp
  intro sc
  apply ayclicMono sc
  simp [CatRel.CatUnion.union] at *
  intro a b h
  rcases h with hImplied | h
  · rcases hImplied with ⟨mid, hpo_amid, htail⟩
    rcases htail with hId | hComp
    · have hmid_eq_b : mid = b := hId.1
      subst hmid_eq_b
      exact Or.inl hpo_amid
    · rcases hComp with ⟨x, hIdMidX, hpo_xb⟩
      have hmid_eq_x : mid = x := hIdMidX.1
      subst hmid_eq_x
      exact Or.inl (X.prePo _ _ _ hpo_amid hpo_xb)
  · rcases h with hxppo | h
    · exact Or.inl hxppo.2
    · rcases h with hrfe | h
      · exact Or.inr (Or.inr (Or.inl hrfe.1))
      · rcases h with hfr | hco
        · exact Or.inr (Or.inr (Or.inl hfr))
        · exact Or.inr (Or.inr (Or.inr hco))
