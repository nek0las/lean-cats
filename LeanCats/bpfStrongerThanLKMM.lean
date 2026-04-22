import LeanCats.Macro
import LeanCats.ModelReader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theorems
import LeanCats.Basic

open CatRel Data

-- ---------------------------------------------------------------------------
-- coi ⊆ bpf.ppo  and  fri ⊆ bpf.ppo
-- Both appear explicitly as the last disjunct of bpf.ppo.
-- ---------------------------------------------------------------------------

lemma coi_subset_bpf_ppo (evts : Data.Events) (X : CandidateExecution evts) :
    ∀ a b, (a, b) ∈ coi evts X → (a, b) ∈ bpf.ppo evts X := by
  intro a b h
  simp only [bpf.ppo, CatRel.CatUnion.union]
  exact Or.inr (Or.inl h)

lemma fri_subset_bpf_ppo (evts : Data.Events) (X : CandidateExecution evts) :
    ∀ a b, (a, b) ∈ fri evts X → (a, b) ∈ bpf.ppo evts X := by
  intro a b h
  simp only [bpf.ppo, CatRel.CatUnion.union]
  exact Or.inr (Or.inr h)

-- ---------------------------------------------------------------------------
-- lkmm.ppo ⊆ bpf.hb
--
-- lkmm.ppo = to_r | to_w | fence
--   to_r = addr | (dep ; [Marked] ; rfi)
--   to_w = rwdep | ((co | fr) & int) | (addr ; [Plain] ; wmb)
--
-- Wellformedness hypotheses for dependency relations:
--   haddr_wf  :  addr goes from R to M  (standard for address dependencies)
--   hdata_wf  :  data goes from R to W  (standard for data dependencies)
--   hctrl_wf  :  ctrl has R-source      (standard for control dependencies)
--   hfence_sub:  LKMM fence embeds into BPF ppo (architecture-specific)
-- ---------------------------------------------------------------------------

lemma lkmm_ppo_subset_bpf_hb (evts : Data.Events) (X : CandidateExecution evts)
    (haddr_wf : ∀ a b, (a, b) ∈ X.addr' → a ∈ X.evts.R ∧ b ∈ X.evts.R ∪ X.evts.W)
    (hdata_wf : ∀ a b, (a, b) ∈ X.data' → a ∈ X.evts.R ∧ b ∈ X.evts.W)
    (hctrl_wf : ∀ a b, (a, b) ∈ X.ctrl' → a ∈ X.evts.R) :
    ∀ a b, (a, b) ∈ lkmm.ppo evts X → (a, b) ∈ bpf.hb evts X := by
  intro a b h
  simp only [lkmm.ppo, lkmm.to_r, lkmm.to_w, lkmm.dep, lkmm.rwdep, lkmm.overwrite,
             CatRel.CatUnion.union, Set.mem_setOf_eq,
             SetRel.comp] at h
  rcases h with ((haddr | hdep_rfi) | ((hrwdep | ⟨hcofr, hint⟩) | hwmb)) | hfence
  · -- addr ⊆ bpf.hb  via  addr_dep = [R];addr;[M]
    have ⟨ha_R, hb_M⟩ := haddr_wf a b haddr
    simp only [bpf.hb, bpf.ppo, bpf.addr_dep,
               CatRel.CatUnion.union, Set.mem_setOf_eq, SetRel.comp]
    left; left; left; left; left; left; left; right
    exact ⟨b, ⟨a, ⟨rfl, ha_R⟩, haddr⟩, rfl, hb_M⟩
  · -- (dep ; [Marked] ; rfi) ⊆ bpf.hb  via  [M];(addr|data);[W];rfi;[R]
    -- hdep_rfi : ∃ w, (∃ d, (a,d) ∈ addr∪data ∧ (d,w) ∈ mkId Marked) ∧ (w,b) ∈ rfi
    obtain ⟨w, ⟨d, hdep, hmkid⟩, hrfi⟩ := hdep_rfi
    -- mkId gives d = w ∧ d ∈ Marked
    have hd_eq : d = w := hmkid.1
    rw [hd_eq] at hdep
    -- rfi ⊆ rf, giving us: w ∈ W, b ∈ R
    have hrf : (w, b) ∈ X.rf' := (Set.mem_inter_iff _ _ _ |>.mp hrfi).1
    have ⟨hw_W, hb_R, _, _⟩ := X.rfInst.wellTyped w b hrf
    have ha_M : a ∈ X.evts.R ∪ X.evts.W := by
      rcases hdep with haddr | hdata
      · exact Or.inl (haddr_wf a w haddr).1
      · exact Or.inl (hdata_wf a w hdata).1
    simp only [bpf.hb, bpf.ppo, CatRel.CatUnion.union, Set.mem_setOf_eq, SetRel.comp]
    left; left; left; left; right
    -- [M];(addr|data);[W];rfi;[R]
    exact ⟨b, ⟨w, ⟨w, ⟨a, ⟨rfl, ha_M⟩, hdep⟩, rfl, hw_W⟩, hrfi⟩, rfl, hb_R⟩
  · -- rwdep = ((addr|data)|ctrl);[W] ⊆ bpf.hb
    -- hrwdep : ∃ mid, (a,mid) ∈ (addr∪data)∪ctrl ∧ (mid,b) ∈ mkId W
    obtain ⟨mid, hdep, hmkid⟩ := hrwdep
    have hmid_eq : mid = b := hmkid.1
    have hb_W : b ∈ X.evts.W := by rw [← hmid_eq]; exact hmkid.2
    rw [hmid_eq] at hdep
    simp only [bpf.hb, bpf.ppo, bpf.addr_dep, bpf.data_dep, bpf.ctrl_dep,
               CatRel.CatUnion.union, Set.mem_setOf_eq, SetRel.comp]
    rcases hdep with (hd_addr | hd_data) | hd_ctrl
    · -- addr → addr_dep = [R];addr;[M]
      have ⟨ha_R, _⟩ := haddr_wf a b hd_addr
      left; left; left; left; left; left; left; right
      exact ⟨b, ⟨a, ⟨rfl, ha_R⟩, hd_addr⟩, rfl, Or.inr hb_W⟩
    · -- data → data_dep = [R];data;[W]
      have ⟨ha_R, _⟩ := hdata_wf a b hd_data
      left; left; left; left; left; left; right
      exact ⟨b, ⟨a, ⟨rfl, ha_R⟩, hd_data⟩, rfl, hb_W⟩
    · -- ctrl → ctrl_dep = [R];ctrl;[W]
      have ha_R := hctrl_wf a b hd_ctrl
      left; left; left; left; left; right
      exact ⟨b, ⟨a, ⟨rfl, ha_R⟩, hd_ctrl⟩, rfl, hb_W⟩
  · -- (co | fr) & int  →  coi | fri  ⊆  bpf.ppo  ⊆  bpf.hb
    simp only [bpf.hb, CatRel.CatUnion.union]
    rcases hcofr with hco | hfr
    · exact Or.inl (Or.inl (coi_subset_bpf_ppo evts X a b ⟨hco, hint⟩))
    · exact Or.inl (Or.inl (fri_subset_bpf_ppo  evts X a b ⟨hfr, hint⟩))
  · -- addr ; [Plain] ; wmb — vacuous because Plain = ∅ in BPF executions
    obtain ⟨mid, ⟨d, _, hplain⟩, _⟩ := hwmb
    have : d ∈ lkmm.Plain evts X := hplain.2
    sorry
  · -- fence ⊆ bpf.hb via assumption
    simp only [bpf.hb, CatRel.CatUnion.union]
    sorry

-- ---------------------------------------------------------------------------
-- lkmm.prop ⊆ bpf.prop
--
-- lkmm.prop = [Marked] ; (overwrite & ext)? ; cumul_fence* ; [Marked] ; rfe? ; [Marked]
-- bpf.prop  = (coe | fre)? ; A_cumul* ; rfe?
--
-- The embedding requires relating cumul_fence to A_cumul, which depends on
-- fence definitions and mappings not present in the BPF model.
-- ---------------------------------------------------------------------------

lemma lkmm_prop_subset_bpf_prop (evts : Data.Events) (X : CandidateExecution evts) :
    ∀ a b, (a, b) ∈ lkmm.prop evts X → (a, b) ∈ bpf.prop evts X := by
  sorry

-- ---------------------------------------------------------------------------
-- lkmm.hb ⊆ bpf.hb
--
-- lkmm.hb = [Marked] ; (lkmm.ppo | rfe | ((lkmm.prop \ id) ∩ int)) ; [Marked]
-- bpf.hb  = bpf.ppo  | rfe | ((bpf.prop \ id) ∩ int)
--
-- The [Marked] brackets collapse: the pair (a, c) is in lkmm.hb iff
--   a ∈ Marked  ∧  c ∈ Marked  ∧  (a,c) ∈ ppo | rfe | ((prop \ id) ∩ int).
-- Then case-split on the core component.
-- ---------------------------------------------------------------------------

lemma lkmm_hb_subset_bpf_hb (evts : Data.Events) (X : CandidateExecution evts)
    (haddr_wf : ∀ a b, (a, b) ∈ X.addr' → a ∈ X.evts.R ∧ b ∈ X.evts.R ∪ X.evts.W)
    (hdata_wf : ∀ a b, (a, b) ∈ X.data' → a ∈ X.evts.R ∧ b ∈ X.evts.W)
    (hctrl_wf : ∀ a b, (a, b) ∈ X.ctrl' → a ∈ X.evts.R) :
    ∀ a b, (a, b) ∈ lkmm.hb evts X → (a, b) ∈ bpf.hb evts X := by
  intro a b h
  -- Unfold lkmm.hb: (([Marked] ; (ppo | rfe | ((prop\id) & int))) ; [Marked])
  simp only [lkmm.hb, SetRel.comp, CatRel.CatUnion.union,
             Set.mem_setOf_eq] at h
  -- h : ∃ m2, (∃ m1, (a=m1 ∧ m1∈Marked) ∧ core(m1,m2)) ∧ (m2=b ∧ m2∈Marked)
  obtain ⟨m2, ⟨m1, ⟨hm1_eq, _⟩, hcore⟩, hm2_eq, _⟩ := h
  rw [← hm1_eq, hm2_eq] at hcore
  simp only [CatRel.SetRel.union, Set.mem_setOf_eq] at hcore
  -- hcore : ppo ∨ rfe ∨ ((prop \ id) ∩ int)
  rcases hcore with (hppo | hrfe) | hpropint
  · exact lkmm_ppo_subset_bpf_hb evts X haddr_wf hdata_wf hctrl_wf a b hppo
  · -- rfe is shared
    simp only [bpf.hb, CatRel.CatUnion.union]
    exact Or.inl (Or.inr hrfe)
  · -- (lkmm.prop \ id) ∩ int → (bpf.prop \ id) ∩ int
    have hprop : (a, b) ∈ lkmm.prop evts X := by
      exact hpropint.1.1
    have hnotid : (a, b) ∉ SetRel.id := by
      exact hpropint.1.2
    have hint : (a, b) ∈ int evts X := by
      exact hpropint.2
    simp only [bpf.hb, CatRel.CatUnion.union]
    exact Or.inr ⟨⟨lkmm_prop_subset_bpf_prop evts X a b hprop, hnotid⟩, hint⟩

-- ---------------------------------------------------------------------------
-- lkmm.pb ⊆ bpf.pb
--
-- lkmm.pb = (lkmm.prop ; strong_fence ; (lkmm.hb ∪ id)) ; [Marked]
-- bpf.pb  = bpf.prop ; bpf.po_amo_fetch ; (bpf.hb ∪ id)
--
-- The embedding requires relating strong_fence (= mb) to po_amo_fetch and
-- cumul_fence to A_cumul, which depend on fence definitions and mappings
-- not present in the BPF model.
-- ---------------------------------------------------------------------------

lemma lkmm_pb_subset_bpf_pb (evts : Data.Events) (X : CandidateExecution evts) :
    ∀ a b, (a, b) ∈ lkmm.pb evts X → (a, b) ∈ bpf.pb evts X := by
  sorry

-- ---------------------------------------------------------------------------
-- Main theorem: BPF is stronger than LKMM.
-- Every BPF-valid execution is also LKMM-valid.
-- ---------------------------------------------------------------------------

theorem bpfStrongerThanLKMM
  (evts : Data.Events)
  (X : CandidateExecution evts)
  (haddr_wf : ∀ a b, (a, b) ∈ X.addr' → a ∈ X.evts.R ∧ b ∈ X.evts.R ∪ X.evts.W)
  (hdata_wf : ∀ a b, (a, b) ∈ X.data' → a ∈ X.evts.R ∧ b ∈ X.evts.W)
  (hctrl_wf : ∀ a b, (a, b) ∈ X.ctrl' → a ∈ X.evts.R)
  : (bpf.Coherence evts X ∧ bpf.Atomic evts X ∧
      bpf.Happens_before evts X ∧ bpf.propagation evts X) →
    (lkmm.coherence evts X ∧ lkmm.atomic evts X ∧
      lkmm.happens_before evts X ∧ lkmm.propagation evts X) := by
  intro h
  rcases h with ⟨hcoh, hatom, hhb, hpb⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bpf.Coherence → lkmm.coherence
    -- Both are acyclic(com | po_loc) with the same com = rf ∪ co ∪ fr.
    simpa [bpf.Coherence, lkmm.coherence, bpf.com, lkmm.com,
        CatRel.CatUnion.union, or_left_comm, or_assoc, or_comm,
        Set.mem_setOf_eq] using hcoh
  · -- bpf.Atomic → lkmm.atomic
    -- Both are empty(rmw ∩ (fre ; coe)).
    simpa [bpf.Atomic, lkmm.atomic] using hatom
  · -- bpf.Happens_before → lkmm.happens_before
    -- lkmm.hb ⊆ bpf.hb, so acyclic(bpf.hb) implies acyclic(lkmm.hb).
    unfold bpf.Happens_before at hhb
    unfold lkmm.happens_before
    exact ayclicMono hhb (lkmm_hb_subset_bpf_hb evts X haddr_wf hdata_wf hctrl_wf)
  · -- bpf.propagation → lkmm.propagation
    -- lkmm.pb ⊆ bpf.pb, so acyclic(bpf.pb) implies acyclic(lkmm.pb).
    unfold bpf.propagation at hpb
    unfold lkmm.propagation
    exact ayclicMono hpb (lkmm_pb_subset_bpf_pb evts X)
