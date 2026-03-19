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
  simp
  intro a b tso

  cases tso with
  | inl h => {
    simp at h
    apply Or.inl
    obtain ⟨l, r⟩ := h
    exact l
  }
  | inr h => {
    obtain ⟨l⟩ := h
    {
      apply Or.inr
      apply Or.inl
      exact l
    }
    {
      rename_i h
      apply Or.inr
      apply Or.inr
      simp [CatRel.CatUnion.union] at *
      aesop
    }
  }
