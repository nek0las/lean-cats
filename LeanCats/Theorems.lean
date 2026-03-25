import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic
open Relation
open CatRel
open Data


-- Relation composition (Relation sequence in cat definition).
lemma internalImpliesPoOrPoMinusOne {e₁ e₂ : Event} (evts : Events) :
  internal evts e₁ e₂ -> e₁ ≠ e₂ -> po evts e₁ e₂ ∨ po evts e₂ e₁ :=
  by
    simp
    intros he₁in he₂in htideq hneq
    simp [po]
    have hidneq : e₁.id ≠ e₂.id :=
      by
        intro hideq
        apply hneq
        apply Iff.mpr
        have h : e₁ = e₂ :=
          by apply (event_id_unique e₁ e₂ hideq)

        apply Iff.intro
        {
          intro h'
          exact h'
        }
        {
          intro h'
          exact h'
        }
        have h : e₁ = e₂ :=
          by apply (event_id_unique e₁ e₂ hideq)

        contradiction

    have hle_or_gt : e₁.id < e₂.id ∨ e₁.id > e₂.id :=
      by
        apply Iff.mp
        apply Nat.ne_iff_lt_or_gt
        exact hidneq

    induction hle_or_gt with
    | inl h => {
      apply Or.inl
      apply And.intro
      {
        aesop
      }
      {
        exact h
      }
    }
    | inr h => {
      apply Or.inr
      apply And.intro
      {
        simp [Eq.comm]
        aesop
      }
      {
        aesop
      }
    }

-- lemma rfAndFrIsCo (evts : Events) (co : Events -> Rel Event Event) (e₁ e₂ e₃ : Event) :
--   (rf.wellformed evts e₁ e₂ ∧ fr evts co e₂ e₃) -> co evts e₁ e₃ :=
--   by
--     intro hrffr
--     have hrf : rf.wellformed evts e₁ e₂ := by apply And.left hrffr
--     have hfr : fr evts co e₂ e₃ := by apply And.right hrffr
--     simp at hfr
--     have hwunique : e₂.act.op = Op.read -> (∃w, isWrite w ∧ rf evts w e₂) ∧ (∀ w₁ w₂, rf evts w₁ e₂ -> rf evts w₂ e₂ -> w₁ = w₂) :=
--     by
--       exact hrf.wExtAndUnique
--
--     simp at *
--     let ⟨w, hw⟩ := hfr
--     -- At this point, what we want to get is w is e₁.
--     have sameW :
--       (∃ w, w.act.op = Op.write ∧ rf evts w e₂)
--       ∧ ∀ (w₁ w₂ : Event), rf evts w₁ e₂ → rf evts w₂ e₂ → w₁ = w₂ :=
--     by
--       apply hwunique
--       apply hrf.rRead
--     have hwe₁ : (e₁ = w) :=
--     by
--       apply And.right sameW
--       {
--         obtain ⟨hrfin, hunique⟩ := hrf
--         exact hrfin
--       }
--       {
--         obtain ⟨left, mid, right⟩ := hw
--         exact mid
--       }
--
--     obtain ⟨left, mid, right⟩ := hw
--     rw [<-hwe₁] at right
--     exact right

-- lemma scIsTransitive (evts : Events) (co : Events -> Rel Event Event) : Transitive (sc evts co) :=
--   by
--     unfold Transitive
--     intro a b c
--     intro hab
--     intro hbc

lemma comIsTransitive
  (evts : Events)
  [h : IsStrictTotalOrder Event (preCo evts)]
  : Transitive (com evts) :=
  by
    unfold Transitive
    intro x y z
    sorry

-- TODO(Zhiyang): Why we don't need asym.
-- class StrictPartialOrder (r : Rel Event Event) extends IsStrictOrder Event r

lemma strictPartialOrderImpliesAcyclic
  {r : Rel Event Event}
  (hr : IsStrictOrder Event r)
  : ∀e, ¬TransGen r e e :=
  by
    rw [Relation.transGen_eq_self]
    {
      apply hr.irrefl
    }
    {
      unfold Transitive
      apply hr.trans
    }

lemma AcyclicImpliesIrreflexive
  {r : Rel Event Event}
  (hnt : ∀e, ¬TransGen r e e)
  : Std.Irrefl r :=
  by
    apply Std.Irrefl.mk
    intro e hre
    exact hnt e (TransGen.single hre)

instance
  {r : Rel Event Event}
  (ht : Transitive r)
  (hnt : ∀e, ¬TransGen r e e)
  : IsStrictOrder Event r where
  irrefl := by
    intros e hre
    apply hnt e
    exact (TransGen.single hre)
  trans := by
    apply ht

@[simp, aesop safe apply]
lemma ayclicMono
  {r₁ r₂ : SetRel Event Event}
  (hacyc : SetRel.Acyclic r₂)
  (hsub : ∀ a b, (a, b) ∈ r₁ -> (a, b) ∈ r₂)
  : SetRel.Acyclic r₁ :=
  by
    have htransub : ∀ a b, TransGen (λ e₁ e₂ ↦ (e₁, e₂) ∈ r₁) a b -> TransGen (λ e₁ e₂ ↦ (e₁, e₂) ∈ r₂) a b :=
      by
        intro a b
        apply TransGen.mono
        apply hsub
    unfold SetRel.Acyclic at *
    intro e hr₁trans
    apply hacyc
    apply htransub
    exact hr₁trans

--- tso : Relation.TransGen
---   (Rel.po evts ∩ (prod W W ∪ prod R (R ∪ W)) ∪ union (external evts ∪ Rel.rf evts) (co evts ∪ Rel.fr evts co)) x x
--- ⊢ Relation.TransGen (fun x y => (Rel.rf evts x y ∨ co evts x y ∨ Rel.fr evts co x y) ∨ Rel.po evts x y) ?x ?x

/-- Composing rf then fr yields co: if `w` reads-from `r`, and `r` is from-read of `w'`,
    then `w` coherence-precedes `w'`.

    Proof sketch: unfolding `fr = rf⁻¹ ; co` gives a witness `w₁` with
    `(w₁, r) ∈ rf` and `(w₁, w') ∈ co`; rf-uniqueness forces `w = w₁`;
    substituting gives `(w, w') ∈ co`. -/
theorem rf_fr_subset_co
  {evts : Events}
  (X : CandidateExecution evts)
  (w r w' : Event)
  (hrf : (w, r) ∈ X.rf)
  (hfr : (r, w') ∈ X.fr) :
  (w, w') ∈ X.co := by
  simp only [CandidateExecution.fr] at hfr
  obtain ⟨w₁, h₁, h₂⟩ := hfr
  simp only [SetRel.inv] at h₁
  exact X.rfInst.unique w w₁ r hrf h₁ ▸ h₂

/-- co is acyclic: no write can coherence-precede itself.
    Follows directly from co being a strict partial order (irrefl + trans). -/
theorem co_acyclic
  {evts : Events}
  (X : CandidateExecution evts) :
  SetRel.Acyclic X.co := by
  let r : Rel Event Event := fun e₁ e₂ => (e₁, e₂) ∈ X.co
  have hiso : IsStrictOrder Event r :=
    { irrefl := fun e h => X.preCo.irrefl e h
      trans  := fun a b c hab hbc => X.preCo.trans a b c hab hbc }
  intro a ha
  exact strictPartialOrderImpliesAcyclic hiso a ha

/-- Composing fr then co yields fr: if `r` is from-read of `w`, and `w` co-precedes `w'`,
    then `r` is from-read of `w'`.
    Proof: unfold fr to get witness `w₀` with `(w₀,r)∈rf` and `(w₀,w)∈co`;
    co-transitivity gives `(w₀,w')∈co`; re-pack as fr. -/
theorem fr_co_subset_fr
  {evts : Events}
  (X : CandidateExecution evts)
  (r w w' : Event)
  (hfr : (r, w) ∈ X.fr)
  (hco : (w, w') ∈ X.co) :
  (r, w') ∈ X.fr := by
  simp only [CandidateExecution.fr] at *
  obtain ⟨w₀, h_inv, h_co⟩ := hfr
  exact ⟨w₀, h_inv, X.preCo.trans w₀ w w' h_co hco⟩
