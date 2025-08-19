import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.LocalToDataset

open SLang
open ENNRealLemmas
open RandomizedResponse

namespace SLang
/- We prove the ln ((1/2 + λ)/(1/2 - λ)) differential privacy bound for our implementation of
   randomized response.
   We first prove the bound for the single-user (local randomizer) version,
   and then apply the lemma in "LocalToDataset" to extend the result to a dataset.-/

/- Final arithmetic bound for the DP proof, by considering eight possible cases. -/
lemma final_bound (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (a a' : T) (b : Bool):
  RRSingleSample query num den h a b / RRSingleSample query num den h a' b
  ≤ (den + 2 * num) / (den - 2 * num) := by
  cases b with
  | true =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                rw[ENNReal.div_self]
                {rw [@Decidable.le_iff_lt_or_eq]
                 cases hnum : num == 0 with
                   | true => simp at hnum
                             apply Or.inr
                             subst hnum
                             simp
                             rw [ENNReal.div_self]
                             norm_num
                             apply pnat_zero_imp_false
                             simp
                   | false => simp at hnum
                              apply Or.inl
                              apply quot_gt_one_rev
                              simp
                              have h1: 0 < (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [@Nat.pos_iff_ne_zero]
                                simp
                                exact hnum
                              have h2: den < den + (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [add_assoc]
                                apply ENNReal.lt_add_right
                                simp
                                norm_num
                                exact hnum

                              simp_all only [pos_add_self_iff, CanonicallyOrderedCommSemiring.mul_pos, Nat.ofNat_pos,
                                Nat.cast_pos, true_and, NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt]
                              apply ENNReal.sub_lt_of_lt_add
                              rw [@Decidable.le_iff_eq_or_lt]
                              right
                              rw [← ENNReal.coe_two]
                              exact_mod_cast h

                              simp_all only}
                {rw [@ENNReal.div_ne_zero]
                 apply And.intro
                 simp
                 intro hd
                 apply False.elim
                 apply pnat_zero_imp_false den hd
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                }
                { simp
                  rw [@ENNReal.div_eq_top]
                  rw[Not]
                  intro b
                  rcases b with ⟨_, br⟩
                  have hh : ¬ den.val = 0 := by simp
                  simp at br
                  rw [Not] at hh
                  apply hh at br
                  exact br
                  rename_i h_1
                  simp_all only [ENNReal.add_eq_top, ENNReal.coe_ne_top, false_or, ne_eq]
                  obtain ⟨left⟩ := h_1
                  norm_cast
                }
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                 simp_all only [NNReal.ofPNat, Nonneg.mk_natCast]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 simp_all only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero,
                   false_or]
                 apply pnat_zero_imp_false
                 simp_all only [ne_eq]
                 apply Aesop.BuiltinRules.not_intro
                 intro a_1
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false
    | false =>
      rw [RRSingleSample_false_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true =>
                 rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                 simp_all only [NNReal.ofPNat, Nonneg.mk_natCast]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [← @ENNReal.div_eq_inv_mul]
                 rw  [← @ENNReal.div_eq_inv_mul]
                 apply ENNReal.div_le_div
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp
                 apply pnat_zero_imp_false
                 simp
                 rw [Not]
                 intro a
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false

      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                 rw[ENNReal.div_self]
                 { rw [@Decidable.le_iff_lt_or_eq]
                   cases hnum : num == 0 with
                   | true => simp at hnum
                             apply Or.inr
                             subst hnum
                             simp
                             rw [ENNReal.div_self]
                             norm_num
                             apply pnat_zero_imp_false
                             simp
                   | false => simp at hnum
                              apply Or.inl
                              apply quot_gt_one_rev
                              simp
                              have h1: 0 < (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [@Nat.pos_iff_ne_zero]
                                simp
                                exact hnum
                              have h2: den < den + (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [add_assoc]
                                apply ENNReal.lt_add_right
                                simp
                                norm_num
                                exact hnum

                              simp_all only [pos_add_self_iff, CanonicallyOrderedCommSemiring.mul_pos, Nat.ofNat_pos,
                                Nat.cast_pos, true_and, NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt]
                              apply ENNReal.sub_lt_of_lt_add
                              rw [@Decidable.le_iff_eq_or_lt]
                              right
                              rw [← ENNReal.coe_two]
                              exact_mod_cast h

                              simp_all only
                  }
                 {simp
                  apply And.intro
                  rw [Not]
                  intro b
                  rw [@Nat.lt_iff_le_and_not_ge] at h
                  rw [@tsub_eq_zero_iff_le] at b
                  rcases h with ⟨hl, hr⟩
                  rw [← ENNReal.coe_two] at b
                  have hh : den.val ≤ 2 * num := by
                    exact_mod_cast b
                  linarith

                  rw [Not]
                  intro a_1
                  norm_cast
                 }
                 { simp
                   rw [@ENNReal.div_eq_top]
                   rw[Not]
                   intro b
                   rcases b with ⟨_, br⟩
                   have hh : ¬ den.val = 0 := by simp
                   simp at br
                   rw [Not] at hh
                   apply hh at br
                   exact br
                   rename_i h_1
                   simp_all only [ENNReal.add_eq_top, ENNReal.coe_ne_top, false_or, ne_eq]
                   obtain ⟨left⟩ := h_1
                   norm_cast
                 }

  | false =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                simp
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [ENNReal.mul_inv]
                simp
                rw [← mul_assoc]
                conv =>
                  enter [1,1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                rw [ENNReal.inv_mul_cancel]
                rw [one_mul]
                rw [ENNReal.inv_mul_cancel]
                rw [ENNReal.le_div_iff_mul_le]
                rw [one_mul]
                simp_all only [tsub_le_iff_right]
                rw [add_assoc]
                have hh (a b : ENNReal) : a ≤ a + b := by simp
                apply hh

                right
                simp_all only [ne_eq, add_eq_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
                  OfNat.ofNat_ne_zero, false_or, not_and]
                intro a_1
                apply Aesop.BuiltinRules.not_intro
                intro a_2
                subst a_2
                simp_all only [mul_zero, PNat.pos]
                have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                contradiction

                left
                norm_num

                simp
                rw [Not]
                intro b
                rw [@Nat.lt_iff_le_and_not_ge] at h
                rw [@tsub_eq_zero_iff_le] at b
                rcases h with ⟨hl, hr⟩
                rw [← ENNReal.coe_two] at b
                have hh : den.val ≤ 2 * num := by
                  exact_mod_cast b
                linarith
                norm_num
                simp
                apply pnat_zero_imp_false
                simp
                rw[Not]
                intro b
                norm_cast
                left
                simp
                rw[Not]
                intro b
                norm_cast
                left
                simp
                apply pnat_zero_imp_false
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 simp
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [← @ENNReal.div_eq_inv_mul]
                 rw  [← @ENNReal.div_eq_inv_mul]
                 apply ENNReal.div_le_div
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp
                 apply pnat_zero_imp_false
                 simp
                 rw [Not]
                 intro a
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false
    | false =>
      rw [RRSingleSample_false_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                simp
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [ENNReal.mul_inv]
                simp
                rw [mul_assoc]
                rw [mul_comm]
                rw [mul_comm]
                rw [← mul_assoc]
                rw [← mul_assoc]
                conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                rw [ENNReal.inv_mul_cancel]
                rw [one_mul]
                simp
                apply pnat_zero_imp_false
                simp
                rw [Not]
                intro b
                norm_cast
                left
                simp
                rw[Not]
                intro b
                norm_cast
                left
                simp
                apply pnat_zero_imp_false
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 simp
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [← mul_assoc]
                 conv =>
                  enter [1,1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [ENNReal.inv_mul_cancel]
                 rw [ENNReal.le_div_iff_mul_le]
                 rw [one_mul]
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 right
                 simp_all only [ne_eq, add_eq_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
                   OfNat.ofNat_ne_zero, false_or, not_and]
                 intro a_1
                 apply Aesop.BuiltinRules.not_intro
                 intro a_2
                 subst a_2
                 simp_all only [mul_zero, PNat.pos]
                 have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                 contradiction
                 left
                 norm_num
                 simp
                 intro b
                 rw [Not]
                 intro
                 have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                 contradiction
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 simp
                 apply pnat_zero_imp_false
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false

/- Instantiation of RRSingleSample as a local randomizer -/
def RRSingle_Local (query : T → Bool) (num: Nat) (den : PNat) (h: 2 * num < den): LocalMechanism T Bool :=
  fun l => ⟨RRSingleSample query num den h l, RRSingleSample_PMF_helper query num den h l⟩

/- Using the "final_bound" lemma above to show that RRSingle_Local is locally differentially private. -/
lemma RR_Local_DP (query : T → Bool) (num : Nat) (den : PNat) (h : 2 * num < den): Local_DP (RRSingle_Local query num den h) (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num))) := by
  rw [Local_DP]
  intro u₁ u₂ y
  simp [RRSingle_Local]
  have h1: RRSingleSample query num den h u₁ y / RRSingleSample query num den h u₂ y ≤ ENNReal.ofReal (Real.exp (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num)))) := by
    calc
    RRSingleSample query num den h u₁ y / RRSingleSample query num den h u₂ y ≤ (↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num) := final_bound query num den h u₁ u₂ y
    _ = ENNReal.ofReal (Real.exp (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num)))) := by rw [final_step_combined num den h]
  apply h1

/- Proof that our implementation of randomized response is ln ((1/2 + λ)/(1/2 - λ))-differentially private.
   The proof is by applying the lemma proven in "LocalToDataset" -/
theorem RRSample_DP (query : T → Bool) (num : Nat) (den : PNat) (h : 2 * num < den): DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num))) := by
  have h1: RRSample_PMF query num den h = local_to_dataset_PMF (RRSingle_Local query num den h) := rfl
  rw [h1]
  apply LocalDP_to_dataset _ _
  simp [RRSingle_Local]
  intro l₁ l₂ h_upd b blen1 i
  have hlen: l₂.length = b.length := by rw[←blen1]; apply Eq.symm (UpdateNeighbour_length h_upd)
  apply Iff.intro
  intro hx
  have h_contr: RRSingleSample query num den h l₁[i.val] b[i.val] = 0 := by aesop
  have h_contr2: RRSingleSample query num den h l₁[i.val] b[i.val] ≠ 0 := RRSingleSample_non_zero query num den h l₁[i.val] b[i.val]
  contradiction
  intro hx
  have h_contr: RRSingleSample query num den h l₂[i.val] b[i.val] = 0 := by aesop
  have h_contr2: RRSingleSample query num den h l₂[i.val] b[i.val] ≠ 0 := RRSingleSample_non_zero query num den h l₂[i.val] b[i.val]
  contradiction
  apply RRSingleSample_finite query num den h
  apply RR_Local_DP
