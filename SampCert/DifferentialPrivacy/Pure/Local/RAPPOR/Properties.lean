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

/- This allows us to use prob_ind_prob in the RAPPOR DP proof -/
lemma RAPPOR_prob_of_ind_prob_PMF {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) (a: List (List Bool)) (k : v.length = a.length) :
  RAPPORSample_PMF n query num den h v a = (∏'(i: Fin v.length), RAPPORSingleSample n query num den h (v.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

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

/- lemma RAPPOR_cancel {T : Type} (n : Nat) (query : T -> Fin n) (num : Nat) (den : PNat) (h : 2 * num < den) (v u : T) (len_eq: (one_hot n query v).length = (one_hot n query u).length) (b : List Bool) (hlen: (one_hot n query u).length = b.length):
  ∏ i : Fin ohu.length, RRSinglePushForward num den h ((one_hot n query v)[i.val]'(by sorry)) (b[↑i.val]'(by sorry))
  / RRSinglePushForward num den h ((one_hot n query u)[↑i.val](by sorry)) (b[↑i.val](by sorry)) = 1 := by sorry -/

lemma arith_1 (num : Nat) (den : PNat) (h : 2 * num < den):
(1 : ENNReal) ≤ ((2⁻¹ + ↑num / ↑(NNReal.ofPNat den)) / (2⁻¹ - ↑num / ↑(NNReal.ofPNat den))) ^ 2 := by
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

lemma reduction_helper1 {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length) (h_users: query u ≠ query v) (i : Fin (one_hot n query u).length):
  RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] /
  RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val] =
  if query v = (finCongr (by aesop) i) then RRSinglePushForward num den h (one_hot n query v)[query v] (b[query v]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[query v] (b[query v]'(by aesop))
  else if query u = (finCongr (by aesop) i) then RRSinglePushForward num den h (one_hot n query v)[query u] (b[query u]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[query u] (b[query u]'(by aesop))
  else 1 := by
  cases hi : (finCongr (by aesop) i) == query v with
  | true => simp at hi
            have h1: i.val = (query v).val := by
              rw [← hi]
              simp
            aesop
  | false => simp at hi
             cases hi2: (finCongr (by aesop) i) == query u with
             | true => simp at hi2
                       have h1: i.val = (query u).val := by
                          rw [← hi2]
                          simp
                       simp [h1, -one_hot]
                       simp_all only [not_false_eq_true, List.getElem_ofFn, Fin.eta, decide_True,
                         decide_False, ↓reduceIte]
                       split
                       next h_1 =>
                         simp_all only [decide_True]
                       next h_1 => simp_all only [decide_False]
             | false => simp at hi2
                        simp_all only [List.getElem_ofFn, finCongr_apply, Fin.getElem_fin, Fin.coe_cast,
                          Fin.eta]
                        split
                        next h_1 => simp_all only [not_true_eq_false]
                        next h_1 =>
                          split
                          next h_2 => simp_all only [not_true_eq_false]
                          next h_2 =>
                          have h1: (one_hot n query v)[i.val]'(by omega) = (one_hot n query u)[i.val]'(by omega) :=
                            by convert one_hot_different_answer_ex_two_contrp' n query v u (finCongr (by aesop) i)
                               aesop
                              -- simp_all only [ne_eq, not_or, not_and]
                          rw [h1]
                          rw [ENNReal.div_self]
                          apply RRSinglePushForward_non_zero
                          apply RRSinglePushForward_finite

lemma reduction_helper2 {T : Type} (n : Nat) (query: T -> Fin n) (f : Bool -> SLang Bool) (v u : T) (b : List Bool) (h_users: query u ≠ query v)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
  (∏ i : Fin (one_hot n query u).length,
    if query v = (finCongr (by aesop) i) then f (one_hot n query v)[query v] (b[query v]'(by aesop)) / f (one_hot n query u)[query v] (b[query v]'(by aesop))
    else if query u = (finCongr (by aesop) i) then f (one_hot n query v)[query u] (b[query u]'(by aesop)) / f (one_hot n query u)[query u] (b[query u]'(by aesop))
    else 1) =
  f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
  * f (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop))
   := by
    simp_all only [finCongr_apply, Fin.getElem_fin, Fin.coe_cast, List.getElem_ofFn, Fin.eta]
    have h4 (g : Fin b.length -> ENNReal) : ∏ i : Fin b.length, g i = ∏ (i ∈ Finset.univ), g i := by aesop
    conv =>
      enter [1]
      rw [@Finset.prod_ite]
      simp [-one_hot]
      rw [@Finset.prod_ite]
      simp [-one_hot]
      -- rw [Finset.prod_ite_ite_one]
      -- rw [Finset.prod_set_coe]
    simp_all only [finCongr_apply, implies_true, List.getElem_ofFn, Fin.eta, decide_True]
    have hblen : b.length = n := by aesop
    have h5 (k : T): Finset.filter (fun x => query k = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)) = {finCongr (by aesop) (query k)} := by aesop
    have h6: (Finset.filter (fun x => query u = Fin.cast (by sorry) x) (Finset.filter (fun x => ¬query v = Fin.cast (by sorry) x) (Finset.univ : Finset (Fin (one_hot n query u).length)))).card = 1 := by
        rw [@Finset.card_eq_one]
        use (finCongr (by aesop) (query u))
        aesop
    have h8: ∏ x ∈ Finset.filter (fun x => query v = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query v).val] (b[(query v).val]'(by sorry)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by sorry))
             = f (one_hot n query v)[(query v).val] (b[(query v).val]'(by sorry)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by sorry)) := by
              subst hblen
              simp_all only [List.getElem_ofFn, Fin.eta, Finset.prod_const]
              conv =>
                enter [1, 2]
                simp
              simp
    have h9: ∏ x ∈ Finset.filter (fun x => query u = Fin.cast (by aesop) x) (Finset.filter (fun x => ¬query v = Fin.cast (by aesop) x) Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query u).val] (b[(query u).val]'(by sorry)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by sorry))
             = f (one_hot n query v)[(query u).val] (b[(query u).val]'(by sorry)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by sorry)) := by
             simp_all only [List.getElem_ofFn, Fin.eta, Finset.prod_const]
             simp
    rw [h8]
    rw [h9]
    rw [@mul_div]

lemma single_DP_reduction {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool) (h_users: query u ≠ query v)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
∏ i : Fin (one_hot n query u).length, RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] / RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val]
 = RRSinglePushForward num den h (one_hot n query v)[(query v).val] (b[(query v).val]'(by sorry)) / RRSinglePushForward num den h (one_hot n query u)[(query v).val] (b[(query v).val]'(by sorry))
 * RRSinglePushForward num den h (one_hot n query v)[(query u).val] (b[(query u).val]'(by sorry)) / RRSinglePushForward num den h (one_hot n query u)[(query u).val] (b[(query u).val]'(by sorry))
 := by
 conv =>
  enter [1, 2, i]
  rw [reduction_helper1 n query num den h v u b ohu_len onhv_len h_users i]
 rw [reduction_helper2 _ _ _ _ _ _ h_users]
 have reduction_helper3:
  ∏ i : Fin (one_hot n query u).length, (if query v = (finCongr (by aesop) i) then 1
    else if query u = (finCongr (by aesop) i) then 1 else 1) = 1 := by simp
 simp_all only [mul_one]
 exact onhv_len

/- This shows that that RAPPOR algorithm applied to a single user is differentially private. -/
lemma RAPPORSingle_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool):
  (RAPPORSingleSample n query num den h v b) / (RAPPORSingleSample n query num den h u b) ≤ ((2⁻¹ + num / den) / (2⁻¹ - num / den))^2 := by
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
              {sorry} /- The statement of arith_1 might have to change...-/
              {
                apply RRSamplePushForward_non_zero
                rw[←hlen]
                exact oh_len
              }
              { apply RRSamplePushForward_finite
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
      rw [single_DP_reduction n query num den h v u b (by aesop) oh_len hlen]
      rw [@mul_div_assoc]
      rw [@sq]
      have exp_eq :  ((2:ENNReal)⁻¹ + num / den) / (2⁻¹ - num / den) = (↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num) := by
        apply ENNRealLemmas.exp_change_form
        exact h
      simp at exp_eq
      rw [exp_eq]
      apply ENNRealLemmas.le_double
      apply RRSamplePushForward_final_bound
      apply RRSamplePushForward_final_bound
      apply RRSinglePushForward_div_finite
      apply RRSinglePushForward_div_finite





      /- now need a version of final_bound for RRPushForward -/
      /- use the "calc" tactic to prove this-/
      /- We should wait for Perryn to give an exact statement of the bound to match RR-/
      intro i
      apply RRSinglePushForward_non_zero
      intro i
      apply RRSinglePushForward_finite
  | false =>
      simp at hlen
      have h1: RRSamplePushForward num den h ohv b = 0 := RAPPORSingleSample_diff_lengths n query num den h v b hlen
      rw [h1]
      rw [@ENNReal.zero_div]
      simp

#check Real.log_rpow -- we'll need this later

lemma num_den_simper (num : Nat) (den : PNat) (h : 2 * num < den):
  num / den  < (2⁻¹ : ℝ)  := by
  rw [@div_lt_iff]
  have h1 : 2 * (num : ℝ) < den.val := by exact_mod_cast h
  have h2: 2 * (num : ℝ) < den := by aesop
  have h3 : 2⁻¹ * (2 * (num : ℝ)) < 2⁻¹ * den := by
    rw [@mul_lt_mul_left]
    apply h2
    aesop
  aesop
  simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, NNReal.coe_pos, Nat.cast_pos]
  exact den.2

lemma log_rw (num : Nat) (den : PNat) (h: 2 * num < den):
  2 * Real.log ((2⁻¹ + ↑num / ↑(NNReal.ofPNat den)) / (2⁻¹ - ↑num / ↑(NNReal.ofPNat den))) = Real.log (((2⁻¹ + ↑num / ↑(NNReal.ofPNat den)) / (2⁻¹ - ↑num / ↑(NNReal.ofPNat den)))^2) := by
    rw [←Real.log_rpow]
    simp
    rw [@div_pos_iff]
    apply Or.inl
    apply And.intro
    norm_num
    rw [@one_div]
    positivity
    norm_num
    simp_all only [one_div]
    convert num_den_simper num den h

lemma exp_rw (num : Nat) (den : PNat) (h: 2 * num < den):
  Real.exp (Real.log (((2⁻¹ + num / den) / (2⁻¹ - num / den))^2)) = ((2⁻¹ + num / den) / (2⁻¹ - num / den))^2 := by
    rw [Real.exp_log]
    rw [@sq_pos_iff]
    rw [@div_ne_zero_iff]
    apply And.intro
    positivity
    simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    rw[sub_eq_zero] at a
    rw [inv_eq_one_div] at a
    rw [div_eq_div_iff] at a
    rw[one_mul] at a
    symm at a
    rw [mul_comm] at a
    sorry
    simp
    aesop


lemma arith_2_helper (num : Nat) (den : PNat) (h : 2 * num < den) :
(((2⁻¹ : ENNReal) + ↑num / den) / (2⁻¹ - ↑num / ↑↑↑den.val)) =
  ENNReal.ofReal ((2⁻¹ + ↑num / ↑↑ den.val) / (2⁻¹ - ↑num / ↑↑↑den)) := by
  have h1: ENNReal.ofReal 2⁻¹ = (2⁻¹ : ENNReal) := by
    field_simp
    rw [ENNReal.ofReal_div_of_pos]
    simp
    linarith
  have h2: (0 : ℝ) ≤ num / den.val := by
   rw [@div_nonneg_iff]
   apply Or.inl
   apply And.intro
   aesop
   aesop
  rw [ENNReal.ofReal_div_of_pos]
  congr
  {
   rw [ennreal_of_nat]
   rw [ennreal_of_pnat]
   rw [ENNReal.ofReal_add]
   rw [ENNReal.ofReal_div_of_pos]
   norm_cast
   rw [h1]
   aesop
   aesop
   aesop
   simp [h2]
  }
  { rw [ENNReal.ofReal_sub]
    rw [h1]
    rw [ENNReal.ofReal_div_of_pos]
    aesop
    simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, NNReal.coe_pos, Nat.cast_pos]
    exact den.2
    simp_all only [NNReal.ofPNat, Nonneg.mk_natCast]
    convert h2
  }
  { rw [@sub_pos]
    convert num_den_simper num den h
  }

lemma arith_2_mult_helper (num : Nat) (den : PNat) (h : 2 * num < den) :
(((2⁻¹ : ENNReal) + ↑num / den) / (2⁻¹ - ↑num / ↑↑↑den.val)) * (((2⁻¹ : ENNReal) + ↑num / den) / (2⁻¹ - ↑num / ↑↑↑den.val)) =
ENNReal.ofReal ((2⁻¹ + ↑num / ↑↑ den.val) / (2⁻¹ - ↑num / ↑↑↑den)) * ENNReal.ofReal ((2⁻¹ + ↑num / ↑↑ den.val) / (2⁻¹ - ↑num / ↑↑↑den)) := by
rw [arith_2_helper num den h]

lemma arith_2 (num : Nat) (den : PNat) (h: 2 * num < den):
   ((2⁻¹ + num / den) / (2⁻¹ - num / den))^2 = ENNReal.ofReal (Real.exp (2 * Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by
    conv =>
      enter [2, 1, 1]
      rw [log_rw]
      rfl
      exact h
    conv =>
      enter [2, 1]
      -- rw [Real.exp_log]
      rw [exp_rw num den h]
    rw [@sq, @sq]
    simp
    rw [ENNReal.ofReal_mul]
    convert arith_2_mult_helper num den h
    {
      rw [@div_nonneg_iff]
      apply Or.inl
      apply And.intro
      {positivity}
      { rw [@sub_nonneg]
        rw [@Decidable.le_iff_lt_or_eq]
        apply Or.inl
        convert num_den_simper num den h
      }
    }

/- This extends the previous DP lemma to a dataset of arbitrary size -/
lemma RAPPORSample_is_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (b : List Bool):
  DP_withUpdateNeighbour (RAPPORSample_PMF n query num den h) (2 * Real.log ((2⁻¹ + num/den) / (2⁻¹ - num/den)))
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
                    ((2⁻¹ + num / den) / (2⁻¹ - num / den)) ^ 2 := by apply RAPPORSingle_DP n query num den h
                    _ = ENNReal.ofReal (Real.exp (2 * Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by rw[←arith_2 num den h]
                  }
                  {
                    intro k bo hbo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_non_zero
                    aesop
                  }
                  { intro k bo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_finite
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
