import LeanCats.Data
import LeanCats.Relations

open Data
open CatRel

/-- Each execution is abstracted to a candidate execution 〈evts , po, rf, co, IW, sr〉 providing
This definination is different with the formal semantics, because the `co` is defined in [stdlib.cat](https://github.com/herd/herdtools7/blob/2a7599f8ecdbde0ed67925daf6534c1a0c26d535/herd-www/cat_includes/stdlib.cat) and
by computation, so should declare it as the base relation. -/
structure CandidateExecution (evts : Events) where
  evts := evts
  idUnique : ∀ (e₁ e₂ : Event),
    e₁ ∈ evts.all → e₂ ∈ evts.all →
    e₁ ≠ e₂ → e₁.id ≠ e₂.id
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
  rfiPo : ∀ (w r : Event),
    (w, r) ∈ rf'
    → w.t_id = r.t_id
    → (w, r) ∈ evts.po

/-- from-reads: always defined as rf⁻¹ ; co, so it is transparent to the kernel. -/
@[simp] def CandidateExecution.fr' {evts : Events} (X : CandidateExecution evts) : SetRel Event Event :=
  X.rf'.inv.comp X.co'

/-- Solve the `idUnique` obligation for concrete finite event sets built from
    explicit event literals. -/
macro "candidateExecution_idUnique" : tactic =>
  `(tactic|
    (all_goals repeat first
      | simp [Data.Events.all] at *
      | (casesm _ ∨ _)
      | subst_vars
      | contradiction
      | omega
      | decide
      | aesop))

/-- Helper term for concrete candidate executions whose event sets are given by
    explicit finite set literals. -/
macro "uniqueId_by_id" : term =>
  `(by
    intro e₁ e₂ he₁ he₂ hne
    candidateExecution_idUnique)

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
