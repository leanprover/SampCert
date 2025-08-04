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
    have h4 (g : Fin b.length -> ENNReal) : ∏ i : Fin b.length, g i = ∏ (i ∈ Finset.univ), g i := by aesop
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

/- Cancellation of terms in the DP proof by using the above two lemmas.-/
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

/- This gives the RAPPOR bound when the algorithm is applied to a single user. -/
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
      apply RRSinglePushForward_div_finite
      apply RRSinglePushForward_div_finite
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
                  rw [reduction_final_RAP n l₁ l₂ x (fun _ => RAPPORSingleSample n query num den h ) hl₁ hl₂ xlen1 _ xlen2]
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
                  | false =>
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
