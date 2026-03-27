import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

defcat <"mips.cat">
defcat <"tsox.cat">

theorem mipsWeakerThanTso
  (evts : Data.Events)
  (X : CandidateExecution evts)
  : tsox.tso evts X → mips.pso evts X :=
by
  intro htso
  unfold tsox.tso at htso
  unfold mips.pso
  simp
  apply ayclicMono_trans htso
  intro a b h
  simp [CatRel.CatUnion.union, Set.mem_setOf_eq] at h
  let rtso : SetRel Data.Event Data.Event :=
    CatRel.CatUnion.union (tsox.implied evts X)
      (CatRel.CatUnion.union (tsox.xppo evts X)
        (CatRel.CatUnion.union (rfe evts X) (CatRel.CatUnion.union X.fr' X.co')))
  change Relation.TransGen (fun e₁ e₂ => (e₁, e₂) ∈ rtso) a b
  rcases h with hppo | h
  · rcases hppo with ⟨hpo, hppo_core⟩
    rcases hppo_core with hpo_rm | hsync_raw
    · have hxppo : (a, b) ∈ tsox.xppo evts X := by
        rcases hpo_rm with ⟨haR, hbM⟩
        rcases hbM with hbR | hbW
        · refine ⟨?_, hpo⟩
          exact Or.inr (Or.inr ⟨haR, hbR⟩)
        · refine ⟨?_, hpo⟩
          exact Or.inr (Or.inl ⟨haR, hbW⟩)
      have hstep : (a, b) ∈ rtso := by
        exact Or.inr (Or.inl hxppo)
      exact Relation.TransGen.single hstep
    · rcases hsync_raw with ⟨mid, hhead, hpo_midb⟩
      rcases hhead with ⟨hpo_amid, hall_sync⟩
      rcases hall_sync with ⟨_, hmid_syncdom⟩
      have hmidSYNC : mid ∈ X.SYNC' := by
        simpa [SetRel.dom_mkId] using hmid_syncdom
      have hsyncInF : X.SYNC' ⊆ X.evts.F := by
        exact X.syncInF
      have hmidF : mid ∈ X.evts.F := hsyncInF hmidSYNC
      have himplied_ab : (a, b) ∈ tsox.implied evts X := by
        unfold tsox.implied
        simp [CatRel.CatUnion.union]
        refine ⟨mid, hpo_amid, ?_⟩
        refine Or.inr ?_
        refine ⟨mid, ?_, hpo_midb⟩
        exact ⟨rfl, Or.inr hmidF⟩
      have hstep : (a, b) ∈ rtso := by
        exact Or.inl himplied_ab
      exact Relation.TransGen.single hstep
  · rcases h with hrfe | h
    · have hstep : (a, b) ∈ rtso := by
        exact Or.inr (Or.inr (Or.inl hrfe))
      exact Relation.TransGen.single hstep
    · rcases h with hfr | hco
      · have hstep : (a, b) ∈ rtso := by
          exact Or.inr (Or.inr (Or.inr (Or.inl hfr)))
        exact Relation.TransGen.single hstep
      · have hstep : (a, b) ∈ rtso := by
          exact Or.inr (Or.inr (Or.inr (Or.inr hco)))
        exact Relation.TransGen.single hstep
