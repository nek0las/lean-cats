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
  po   := evts.po
  [prePo: wellformed.po po]
  rf   : SetRel Event Event
  rfInst : wellformed.rf evts rf
  co   : SetRel Event Event
  [preCo : wellformed.co evts co]
  rmw  : SetRel Event Event
  [preRMW : wellformed.rmw evts rmw]
  wmb  : SetRel Event Event
  data : SetRel Event Event
  addr : SetRel Event Event
  ctrl : SetRel Event Event
  fence : SetRel Event Event
  mb : SetRel Event Event
  uniqueId : ∀ (e₁ e₂ : Event),
    e₁ ∈ evts.all → e₂ ∈ evts.all
    -> e₁ ≠ e₂
    → e₁.id ≠ e₂.id

/-- from-reads: always defined as rf⁻¹ ; co, so it is transparent to the kernel. -/
@[simp] def CandidateExecution.fr {evts : Events} (X : CandidateExecution evts) : SetRel Event Event :=
  X.rf.inv.comp X.co
