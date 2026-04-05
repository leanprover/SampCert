import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Properties.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Properties.Arithmetic
import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Properties.PMFProof
namespace RAPPOR

open RandomizedResponse
open SLang

/- In this file, we show that the One-Time Basic RAPPOR algorithm
   is ε-differentially private with ε = 2 ln (1/2 + λ)/(1/2 - λ). -/

/- This allows us to use prob_ind_prob in the RAPPOR DP proof -/
lemma RAPPOR_prob_of_ind_prob_PMF {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) (a: List (List Bool)) (k : v.length = a.length) :
  RAPPORSample_PMF n query num den h v a = (∏'(i: Fin v.length), RAPPORSingleSample n query num den h (v.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- Uses the one-hot-encoding lemmas to rewrite a quotient of RRSinglePushForward applications into an if-then-else statement -/
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
                          rw [h1]
                          rw [ENNReal.div_self]
                          apply RRSinglePushForward_non_zero
                          apply RRSinglePushForward_finite

/- Rewrites the if-then-else statement from above into a simpler form, with most terms cancelled. -/
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
    have _ (g : Fin b.length -> ENNReal) : ∏ i : Fin b.length, g i = ∏ (i ∈ Finset.univ), g i := by aesop
    conv =>
      enter [1]
      rw [@Finset.prod_ite]
      simp [-one_hot]
      rw [@Finset.prod_ite]
      simp [-one_hot]
    simp_all only [finCongr_apply, implies_true, List.getElem_ofFn, Fin.eta, decide_True]
    have hblen : b.length = n := by aesop
    have h5 (k : T): Finset.filter (fun x => query k = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)) = {finCongr (by aesop) (query k)} := by aesop
    have h6: (Finset.filter (fun x => query u = Fin.cast (by aesop) x) (Finset.filter (fun x => ¬query v = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)))).card = 1 := by
        rw [@Finset.card_eq_one]
        use (finCongr (by aesop) (query u))
        aesop
    have h8: ∏ x ∈ Finset.filter (fun x => query v = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
             = f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop)) := by
              subst hblen
              simp_all only [List.getElem_ofFn, Fin.eta, Finset.prod_const]
              conv =>
                enter [1, 2]
                simp
              simp
    have h9: ∏ x ∈ Finset.filter (fun x => query u = Fin.cast (by aesop) x) (Finset.filter (fun x => ¬query v = Fin.cast (by aesop) x) Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query u).val] (b[(query u).val]'(by
             simp_all only [List.getElem_ofFn, Fin.eta, decide_True, decide_False, Fin.is_lt])) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by
             simp_all only [one_hot, List.getElem_ofFn, Fin.eta, decide_True, decide_False, Fin.is_lt]))
             = f (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop)) := by
             simp_all only [List.getElem_ofFn, Fin.eta, decide_True, Finset.prod_const]
             simp
    rw [h8]
    rw [h9]
    rw [@mul_div]

/- Cancellation of terms for the single-user DP proof by using the above two lemmas.-/
lemma single_DP_reduction {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool) (h_users: query u ≠ query v)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
∏ i : Fin (one_hot n query u).length, RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] / RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val]
 = RRSinglePushForward num den h (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
 * RRSinglePushForward num den h (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop))
 := by
 conv =>
  enter [1, 2, i]
  rw [reduction_helper1 n query num den h v u b ohu_len onhv_len h_users i]
 rw [reduction_helper2 _ _ _ _ _ _ h_users]
 simp_all only [mul_one]
 exact onhv_len

/- This gives the RAPPOR DP bound when the algorithm is applied to a single user. -/
lemma RAPPORSingle_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool):
  (RAPPORSingleSample n query num den h v b) / (RAPPORSingleSample n query num den h u b) ≤ ((2⁻¹ + num / den) / (2⁻¹ - num / den))^2 := by
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
              {apply arith_1 _ _ h}
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
      rw [prod_over_prod]
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

/- Instantiation of RAPPOR as a local randomizer -/
def RAPPORSingle_Local (n : Nat) (query : T → Fin n) (num: Nat) (den : PNat) (h: 2 * num < den): LocalMechanism T (List Bool) :=
  fun l => ⟨RAPPORSingleSample n query num den h l, RAPPORSingleSample_PMF_helper query num den h l⟩

/- Proof of Local DP for RAPPOR, using the single-DP bound above. -/
lemma RAPPOR_Local_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den):
  Local_DP (RAPPORSingle_Local n query num den h) (2 * Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den))) := by
  rw [Local_DP]
  intro u₁ u₂ y
  simp [RAPPORSingle_Local]
  calc
   RAPPORSingleSample n query num den h u₁ y /
   RAPPORSingleSample n query num den h u₂ y ≤
   ((2⁻¹ + num / den) / (2⁻¹ - num / den)) ^ 2 := RAPPORSingle_DP n query num den h _ _ _
   _ = ENNReal.ofReal (Real.exp (2 * Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by rw[←arith_2 num den h]

/- Proof of the differential privacy bound for our implementation of Basic One-Time RAPPOR, using
   the lemma in "LocalToDataset."-/
theorem RAPPORSample_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (b : List Bool):
  DP_withUpdateNeighbour (RAPPORSample_PMF n query num den h) (2 * Real.log ((2⁻¹ + num/den) / (2⁻¹ - num/den)))
   := by
   have h1: RAPPORSample_PMF n query num den h = local_to_dataset_PMF (RAPPORSingle_Local n query num den h) := rfl
   rw [h1]
   apply LocalDP_to_dataset _ _
   {intro l₁ l₂ b k bo i
    apply Iff.intro
    simp [RAPPORSingle_Local]
    intro h0
    apply RAPPORSingleSample_diff_lengths
    apply RAPPORSingleSample_zero_imp_diff_lengths at h0
    simp [one_hot, h0]
    intro h0
    apply RAPPORSingleSample_diff_lengths
    apply RAPPORSingleSample_zero_imp_diff_lengths at h0
    simp [←ne_eq]
    apply h0
   }
   {
    intro k bo
    exact PMF.apply_ne_top (RAPPORSingle_Local n query num den h k) bo
   }
   {apply RAPPOR_Local_DP n query num den h}

end RAPPOR
