import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Basic

namespace RAPPOR

open RandomizedResponse
open SLang

/- In the RAPPOR algorithm with n possible responses, the probability of an output of different length than n is zero.-/
lemma RAPPORSingleSample_diff_lengths [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : T) (l₂ : List Bool) (hlen : (one_hot n query l₁).length ≠ l₂.length):
  RAPPORSingleSample n query num den h l₁ l₂= 0 := by
  rw [RAPPORSingleSample]
  apply RRSamplePushForward_diff_lengths num den h (one_hot n query l₁) l₂ hlen


/- The same "diff_lenghts" theorem as above, but extended to the entire dataset. -/
lemma RAPPORSample_diff_lengths [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : List T) (x : List (List Bool)) (hlen : l₁.length ≠ x.length):
  RAPPORSample n query num den h l₁ x = 0 := by
  induction l₁ generalizing x with
  | nil => simp [RAPPORSample, -mapM]
           aesop
  | cons hd tl ih =>
  simp [RAPPORSample, -mapM]
  simp [RAPPORSample, -mapM] at ih
  intro b
  apply Or.inr
  intro y hy
  subst hy
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

/- The next few lemmas are helper lemmas to simplify proofs involving one-hot encodings.
-/
lemma one_hot_same_answer {T : Type} (n : Nat) (query: T -> Fin n) (v u : T) (h : query v = query u) :
  one_hot n query v = one_hot n query u := by
    simp
    rw [h]

lemma one_hot_same_answer_index {T : Type} (n : Nat) (query: T -> Fin n) (v : T) (j : Fin n) :
  (one_hot n query v)[j]'(by simp) = true ↔ query v = j := by
    simp [one_hot]

lemma one_hot_different_answer {T : Type} (n : Nat) (query: T -> Fin n) (v u : T) (h : query u ≠ query v):
  (one_hot n query v)[query v]'(by simp) ≠ (one_hot n query u)[query v]'(by simp) := by
    simp
    rw [← @Ne.eq_def]
    exact h

lemma one_hot_different_answer_ex_two {T : Type} (n : Nat) (query: T -> Fin n) (v u : T) (j : Fin n) (h: query v ≠ query u):
  (one_hot n query v)[j]'(by simp) ≠ (one_hot n query u)[j]'(by simp) ↔ query v = j ∨ query u = j := by
    simp [one_hot]
    apply Iff.intro
    { intro ha
      by_contra hb -- actually aesop can take it from here
      rw [Mathlib.Tactic.PushNeg.not_or_eq] at hb
      apply ha
      apply Iff.intro
      intro hc
      apply And.left at hb
      contradiction
      intro hc
      apply And.right at hb
      contradiction
    }
    { intro ha
      cases ha with
      | inl h1 => aesop
      | inr h1 => aesop
    }

lemma one_hot_different_answer_ex_two_contrp {T : Type} (n : Nat) (query: T -> Fin n) (v u : T) (j : Fin n) (h: query v ≠ query u):
  (one_hot n query v)[j]'(by simp) = (one_hot n query u)[j]'(by simp) ↔ query v ≠ j ∧ query u ≠ j := by
    have h1: query v ≠ j ∧ query u ≠ j ↔ ¬ (query v = j ∨ query u = j) := by simp_all only [ne_eq, not_or]
    rw [h1]
    rw [←one_hot_different_answer_ex_two n query v u j h]
    simp

lemma one_hot_different_answer_ex_two_contrp' {T : Type} (n : Nat) (query: T -> Fin n) (v u : T) (j : Fin n) (h: query v ≠ query u):
  (one_hot n query v)[j.val]'(by simp) = (one_hot n query u)[j.val]'(by simp) ↔ query v ≠ j ∧ query u ≠ j := by
  have h1: (one_hot n query v)[j.val]'(by simp) = (one_hot n query v)[j]'(by simp) := by simp
  have h2: (one_hot n query u)[j.val]'(by simp) = (one_hot n query u)[j]'(by simp) := by simp
  rw [h1, h2]
  rw [one_hot_different_answer_ex_two_contrp n query v u j h]

/- RRSamplePushForward gives a non-zero probability for an output of the same length.
   This is needed in the DP proof.
-/
lemma RRSamplePushForward_non_zero (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) (b : List Bool) (k: l.length = b.length):
  RRSamplePushForward num den h l b ≠ 0 := by
  rw [RRSamplePushForward]
  rw [prod_of_ind_prob _ _ _ _ k]
  rw [@tprod_fintype]
  rw [@Finset.prod_ne_zero_iff]
  intro a _
  apply RRSinglePushForward_non_zero

lemma RAPPORSingleSample_non_zero [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : T) (l₂ : List Bool) (hlen : n = l₂.length):
  RAPPORSingleSample n query num den h l₁ l₂ ≠ 0 := by
  rw [RAPPORSingleSample]
  apply RRSamplePushForward_non_zero num den h (one_hot n query l₁) l₂ (by simp[hlen])

lemma RAPPORSingleSample_zero_imp_diff_lengths [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : T) (l₂ : List Bool)
  (hlen: RAPPORSingleSample n query num den h l₁ l₂ = 0): n ≠ l₂.length := by
  by_contra hx
  have h_contr: RAPPORSingleSample n query num den h l₁ l₂ ≠ 0 := RAPPORSingleSample_non_zero n query num den h l₁ l₂ (by simp[hx])
  contradiction

/- RRSamplePushForward is always finite. This is needed in the DP proof. -/
lemma RRSamplePushForward_finite (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) (b : List Bool):
  RRSamplePushForward num den h l b ≠ ⊤ := by
  cases hlen: l.length == b.length with
  | true =>
    simp at hlen
    unfold RRSamplePushForward
    rw [prod_of_ind_prob _ _ _ _ hlen]
    rw [@tprod_fintype]
    apply ENNRealLemmas.Finset.prod_ne_top_fin
    intro i
    apply RRSinglePushForward_finite
  | false =>
    simp at hlen
    have hzero: RRSamplePushForward num den h l b = 0 := RRSamplePushForward_diff_lengths num den h l b hlen
    rw [hzero]
    simp

/- The quotient of two products is the product of the quotients, under the condition that the denominators are non-zero and non-infinite -/
  /- This is needed in the DP proof -/
  lemma prod_over_prod (n : Nat) (f : Fin n -> ENNReal) (g : Fin n -> ENNReal)(nonzero: ∀i, g i ≠ 0)(noninf: ∀i, g i ≠ ⊤):
  (∏ i : Fin n, f i) / (∏ i : Fin n, g i) = ∏ i : Fin n, (f i / g i) := by
  induction n with
  | zero => simp
  | succ m ih =>
    conv =>
      enter[2]
      simp [@Fin.prod_univ_add]
    rw[← ih]
    simp [@Fin.prod_univ_add]
    conv =>
      enter[1]
      rw[div_eq_mul_inv]
      rw[ENNReal.mul_inv]
      rw[mul_assoc]
      conv =>
        enter[2]
        rw[mul_comm]
      rw[← mul_assoc]
      rw[← mul_assoc]
      conv =>
        enter [1,1]
        rw[mul_comm]
        rw[← ENNReal.div_eq_inv_mul]
      rw[mul_assoc]
      rw[← ENNReal.div_eq_inv_mul]
      rfl
      apply Or.inr
      apply noninf
      apply Or.inr
      apply nonzero
    intro i
    apply nonzero
    intro i
    apply noninf
