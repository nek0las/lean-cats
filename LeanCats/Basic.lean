import LeanCats.Data
import LeanCats.Relations

open Data
open CatRel

/-- Each execution is abstracted to a candidate execution 〈evts , po, rf, co, IW, sr〉 providing
This definination is different with the formal semantics, because the `co` is defined in [stdlib.cat](https://github.com/herd/herdtools7/blob/2a7599f8ecdbde0ed67925daf6534c1a0c26d535/herd-www/cat_includes/stdlib.cat) and
by computation, so should declare it as the base relation. -/
structure CandidateExecution (evts : Events) where
  evts := evts
  idUnique := ∀ e₁ e₂ : Event, (e₁ ∈ evts ∧ e₂ ∈ evts) -> e₁.id ≠ e₂.id
  po'   := evts.po
  [prePo: wellformed.po po']
  rf'   : SetRel Event Event := ∅
  rfInst : wellformed.rf evts rf'
  co'   : SetRel Event Event := ∅
  [preCo : wellformed.co evts co']
  rmw'  : SetRel Event Event := ∅
  [preRMW : wellformed.rmw evts rmw']
  wmb'  : SetRel Event Event := ∅
  data' : SetRel Event Event := ∅
  addr' : SetRel Event Event := ∅
  ctrl' : SetRel Event Event := ∅
  fence' : SetRel Event Event := ∅
  mb' : SetRel Event Event := ∅
  SYNC' : Set Event := ∅
  -- Specific fence event sets depend on the test architecture,
  -- their name is always uppercase and derives from the mnemonic of the instruction that generates them.
  syncInF : ∀ (e : Event), e ∈ SYNC' → e ∈ evts.F
  uniqueId : ∀ (e₁ e₂ : Event),
    e₁ ∈ evts.all → e₂ ∈ evts.all
    -> e₁ ≠ e₂
    → e₁.id ≠ e₂.id
  -- Internal reads-from implies program order: if a write and its read
  -- are on the same thread, the write must precede the read in po.
  rfiPo : ∀ (w r : Event),
    (w, r) ∈ rf'
    → w.t_id = r.t_id
    → (w, r) ∈ evts.po

/-- from-reads: always defined as rf⁻¹ ; co, so it is transparent to the kernel. -/
@[simp] def CandidateExecution.fr' {evts : Events} (X : CandidateExecution evts) : SetRel Event Event :=
  X.rf'.inv.comp X.co'

/-- The `uniqueId` field of any `CandidateExecution`: since `event_id_unique` makes identity
    determined solely by ID, any two distinct events must have distinct IDs. -/
theorem uniqueId_by_id (evts : Events) :
    ∀ (e₁ e₂ : Event), e₁ ∈ evts.all → e₂ ∈ evts.all → e₁ ≠ e₂ → e₁.id ≠ e₂.id :=
  fun _ _ _ _ hne hid => hne (Data.event_id_unique _ _ hid)

/-- Tactic for proving the `rfiPo` and `coWR` obligations of a `CandidateExecution`
    for concrete litmus tests with finite event sets.

    Strategy: unfold all set memberships with standard `Set` simp lemmas plus any
    user-supplied lemmas (typically the `co` and `evts` `@[simp]` definitions), then
    close by `omega` (handles numeric contradictions on IDs / thread IDs) with
    `simp_all` as a pre-processing step when `omega` alone is insufficient. -/
macro "candidateExecution_wf" : tactic =>
  `(tactic|
    (all_goals repeat first
       | simp at *
         aesop
       | (casesm _ ∈ _
          aesop)))
