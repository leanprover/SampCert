import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.RandomizedResponseMain
import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Reduction

namespace RAPPOR

open RandomizedResponse
open SLang

/- In this file, we show normalization for the One-Time Basic RAPPOR Algorithm.
-/

/- Normalization of the single-user RAPPOR, which essentially relies on the normalization property
   of randomized response. -/
lemma RAPPORSingleSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : T) :
  HasSum (RAPPORSingleSample n query num den h v) 1 := by
    rw [RAPPORSingleSample]
    apply RRSamplePushForward_PMF_helper

/- Extension to the multi-user RAPPOR, which follows from our normalization lemma. -/
lemma RAPPORSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) :
  HasSum (RAPPORSample n query num den h v) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    unfold RAPPORSample
    apply Norm_func_norm_on_list
    intro a
    rw [← Summable.hasSum_iff ENNReal.summable]
    apply RAPPORSingleSample_PMF_helper query num den h a

/- Promotion of RAPPOR to a PMF-/
def RAPPORSample_PMF [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) : PMF (List (List Bool)) :=
  ⟨RAPPORSample n query num den h v, RAPPORSample_PMF_helper query num den h v⟩

/- In the RAPPOR algorithm with n possible responses, the probability of an output of different length than n is zero.-/
lemma RAPPORSingleSample_diff_lengths [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : T) (l₂ : List Bool) (hlen : (one_hot n query l₁).length ≠ l₂.length):
  RAPPORSingleSample n query num den h l₁ l₂= 0 := by
  rw [RAPPORSingleSample]
  apply RRSamplePushForward_diff_lengths num den h (one_hot n query l₁) l₂ hlen
/- The same as above, but extended to the entire dataset. -/
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
lemma List.ofFn_rw {T : Type} (n : Nat) (f : Fin n -> T) (i : Fin n):
  (List.ofFn f)[i] = f i := by
  simp [List.ofFn_eq_map]

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

/- This allows us to use prob_ind_prob in the RAPPOR DP proof -/
lemma RAPPOR_prob_of_ind_prob_PMF {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) (a: List (List Bool)) (k : v.length = a.length) :
  RAPPORSample_PMF n query num den h v a = (∏'(i: Fin v.length), RAPPORSingleSample n query num den h (v.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- RRSamplePushForward gives a non-zero probability for an output of the same length.
   This is needed in the DP proof.
-/
lemma RRSamplePushForward_non_zero {T : Type} (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) (b : List Bool) (k: l.length = b.length):
  RRSamplePushForward num den h l b ≠ 0 := by
  rw [RRSamplePushForward]
  rw [prod_of_ind_prob _ _ _ _ k]
  rw [@tprod_fintype]
  rw [@Finset.prod_ne_zero_iff]
  intro a _
  apply RRSinglePushForward_non_zero

/- RRSamplePushForward is always finite. This is needed in the DP proof. -/
lemma RRSamplePushForward_finite {T : Type} (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) (b : List Bool):
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

lemma prod_over_prod (n : Nat) (f : Fin n -> ENNReal) (g : Fin n -> ENNReal):
  (∏ i : Fin n, f i) / (∏ i : Fin n, g i) = ∏ i : Fin n, (f i / g i) := by
   sorry

/- lemma RAPPOR_cancel {T : Type} (n : Nat) (query : T -> Fin n) (num : Nat) (den : PNat) (h : 2 * num < den) (v u : T) (len_eq: (one_hot n query v).length = (one_hot n query u).length) (b : List Bool) (hlen: (one_hot n query u).length = b.length):
  ∏ i : Fin ohu.length, RRSinglePushForward num den h ((one_hot n query v)[i.val]'(by sorry)) (b[↑i.val]'(by sorry))
  / RRSinglePushForward num den h ((one_hot n query u)[↑i.val](by sorry)) (b[↑i.val](by sorry)) = 1 := by sorry -/

lemma arith_1 (num : Nat) (den : PNat) (h : 2 * num < den):
(1 : ENNReal) ≤ ((1 / 2 + ↑num / ↑(NNReal.ofPNat den)) / (1 / 2 - ↑num / ↑(NNReal.ofPNat den))) ^ 2 := by
               rw [@sq]
               simp
               cases frac_zero : num/den.val == (0:ENNReal) with
               | true =>
                simp_all only [beq_iff_eq]
                rw [@Decidable.le_iff_lt_or_eq]
                right
                simp_all only [beq_eq_false_iff_ne, ne_eq, ENNReal.div_eq_zero_iff,
                 Nat.cast_eq_zero, ENNReal.natCast_ne_top, or_false, Nat.cast_mul, Nat.cast_ofNat]
                rw [← ENNReal.coe_two]
                norm_cast
                simp
                rw [ENNReal.div_self]
                simp
                simp
               | false =>
                rw [@Decidable.le_iff_lt_or_eq]
                left
                apply ENNRealLemmas.quot_gt_one_rev
                apply ENNRealLemmas.sub_le_add_ennreal
                aesop
                rw [@ENNReal.le_inv_iff_mul_le]
                rw [@ENNReal.div_eq_inv_mul]
                rw [mul_assoc]
                rw [mul_comm]
                rw [← @ENNReal.le_inv_iff_mul_le]
                simp
                rw [@Decidable.le_iff_lt_or_eq]
                left
                rw [@Nat.cast_comm]
                norm_cast
                simp_all only [beq_eq_false_iff_ne, ne_eq, ENNReal.div_eq_zero_iff,
                  Nat.cast_eq_zero, ENNReal.natCast_ne_top, or_false, Nat.cast_mul, Nat.cast_ofNat]
                rw [← ENNReal.coe_two]
                norm_cast
                simp

/- Good tip: use finCongr for re-indexing... -/
lemma reindex (α β : Type) (l v : List α) (b : List β) (h1 : l.length = v.length) (h2 : l.length = b.length)
  (f : α -> β -> ENNReal):
  ∏ (i : Fin l.length), f l[i] b[i] = ∏ (i : Fin v.length), f l[i] b[i] := by
   apply Fintype.prod_equiv (finCongr h1)
   intro x
   rfl

lemma single_DP_reduction {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
∏ i : Fin (one_hot n query u).length, RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] / RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val]
 = RRSinglePushForward num den h (one_hot n query v)[(query v).val] (b[(query v).val]'(by sorry)) / RRSinglePushForward num den h (one_hot n query u)[(query v).val] (b[(query v).val]'(by sorry))
 * RRSinglePushForward num den h (one_hot n query u)[(query u).val] (b[(query u).val]'(by sorry)) / RRSinglePushForward num den h (one_hot n query u)[(query u).val] (b[(query u).val]'(by sorry))
 := by sorry

/- This shows that that RAPPOR algorithm applied to a single user is differentially private. -/
lemma RAPPORSingle_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool):
  (RAPPORSingleSample n query num den h v b) / (RAPPORSingleSample n query num den h u b) ≤ ((1/2 + num / den) / (1/2 - num / den))^2 := by
  -- probably want to restate the bound in an arithmetically equivalent way
  simp_all only [RAPPORSingleSample]
  set ohv := one_hot n query v
  set ohu := one_hot n query u
  have oh_len: ohu.length = ohv.length := by simp[ohv, ohu]
  cases hlen: ohv.length == b.length with
  | true =>
   simp at hlen
   cases h_eq: query v == query u with
    | true => simp at h_eq
              have same_answer: ohv = ohu := one_hot_same_answer n query v u h_eq
              rw [same_answer]
              rw [@ENNReal.div_self]
              {exact arith_1 num den h} /- The statement of arith_1 might have to change...-/
              {
                apply RRSamplePushForward_non_zero
                exact T
                rw[←hlen]
                exact oh_len
              }
              { apply RRSamplePushForward_finite
                exact T
              }
    | false =>
      simp at h_eq
      simp_all only [RRSamplePushForward]
      rw [prod_of_ind_prob _ _ _ _ hlen]
      rw [prod_of_ind_prob _ _ _ _ oh_len]
      simp_all [@tprod_fintype]
      have len_eq: ohu.length = ohv.length := by aesop
      have index_1: ∏ i : Fin ohv.length, RRSinglePushForward num den h ohv[i.val] b[i.val] =
                    ∏ i : Fin ohu.length, RRSinglePushForward num den h ohv[i.val] b[i.val] := by
                      apply reindex
                      symm at len_eq
                      exact len_eq
                      exact hlen
      rw [index_1]
      rw [prod_over_prod] -- this needs proving
      simp_all only [ohv, ohu]
      rw [single_DP_reduction n query num den h v u b oh_len hlen]
      #check RRSamplePushForward_final_bound
      /- now need a version of final_bound for RRPushForward -/
      /- use the "calc" tactic to prove this-/
      sorry
  | false =>
      simp at hlen
      have h1: RRSamplePushForward num den h ohv b = 0 := RAPPORSingleSample_diff_lengths n query num den h v b hlen
      rw [h1]
      rw [@ENNReal.zero_div]
      simp


#check Real.log_rpow -- we'll need this later

/- This extends the previous lemma to a dataset of arbitrary size -/
lemma RAPPORSample_is_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (b : List Bool):
  DP_withUpdateNeighbour (RAPPORSample_PMF n query num den h) (2 * Real.log ((den + 2 * num) / (den - 2 * num)))
   := by
      apply singleton_to_event_update
      intros l₁ l₂ h_adj x
      cases xlen1 : l₁.length == x.length with
      | true => simp at xlen1
                have xlen2: l₂.length = x.length := by
                  rw [←xlen1]
                  rw[←UpdateNeighbour_length h_adj]
                rw[RAPPOR_prob_of_ind_prob_PMF n query num den h l₁ x xlen1]
                rw[RAPPOR_prob_of_ind_prob_PMF n query num den h l₂ x xlen2]
                cases h_adj with
                | Update hl₁ hl₂ =>
                  rename_i a y c z
                  simp
                  cases x_indices: (∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by apply valid_index4 _ hl₂; apply xlen2)).length = n) == true with
                  | true =>
                  simp at x_indices
                  /- Now we need to apply the generalized reduction lemma,
                  and then do some arithmetic. -/
                  have valid_index5: a.length < l₁.length := by
                    rw [hl₁]
                    rw [@List.length_append]
                    simp_all only [List.append_assoc, List.singleton_append, List.length_append, List.length_cons,
                      List.length_singleton]
                    linarith
                  have valid_index6: a.length < x.length := by
                    rw [←xlen1]
                    exact valid_index5
                  have valid_index7: a.length < l₂.length := by
                    rw [xlen2]
                    exact valid_index6
                  rw [reduction_final_RAP n l₁ l₂ x (fun f => RAPPORSingleSample n query num den h ) hl₁ hl₂ xlen1 _ xlen2]
                  { calc
                    RAPPORSingleSample n query num den h (l₁[a.length]'(valid_index5)) (x[a.length]'(valid_index6)) /
                    RAPPORSingleSample n query num den h (l₂[a.length]'(valid_index7)) (x[a.length]'(valid_index6)) ≤
                    ((1/2 + num / den) / (1/2 - num / den)) ^ 2 := by apply RAPPORSingle_DP n query num den h
                    _ ≤ ENNReal.ofReal (Real.exp (2 * Real.log ((↑↑↑den + 2 * ↑num) / (↑↑↑den - 2 * ↑num)))) := by sorry
                  }
                  {
                    intro k bo hbo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_non_zero
                    exact T
                    aesop
                  }
                  { intro k bo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_finite
                    exact T
                  }
                  {apply x_indices}
                  | false => /- This part of the proof is completely disgusting, I am not proud of it -/
                  simp at x_indices
                  cases x_indices with
                  | intro i hi =>
                  have numerator_zero: (∏' (i : Fin l₁.length), RAPPORSingleSample n query num den h l₁[i.val] x[i.val]) = 0 := by
                    rw [@tprod_fintype]
                    rw[Finset.prod_eq_zero_iff]
                    norm_num
                    have hl1len:l₁.length > 0 := by
                     rw[hl₁]
                     rw [@List.length_append]
                     aesop
                    use (Fin.ofNat' i.val (hl1len))
                    apply RAPPORSingleSample_diff_lengths n query num den h
                    simp
                    have h_coe: i.val % l₁.length = i.val := by
                     rw [Nat.mod_eq]
                     have hival: i.val < l₁.length := by
                      rw [xlen1]
                      apply valid_index4 _ hl₂
                      exact xlen2
                     aesop
                    conv =>
                     enter[1, 2, 1, 2]
                     rw[h_coe]
                    aesop
                  rw [numerator_zero]
                  rw [@ENNReal.zero_div]
                  simp
      | false => simp at xlen1
                 rw [←Ne.eq_def] at xlen1
                 have numerator_zero: RAPPORSample_PMF n query num den h l₁ x = 0 := RAPPORSample_diff_lengths n query num den h l₁ x xlen1
                 rw [numerator_zero]
                 rw [@ENNReal.zero_div]
                 simp

end RAPPOR
