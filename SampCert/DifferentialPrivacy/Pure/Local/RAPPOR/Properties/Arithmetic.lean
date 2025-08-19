import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Basic

open SLang
open ENNRealLemmas
open RandomizedResponse

namespace RAPPOR

/- Mathematically trivial arithmetical steps for the Proof of DP,
   together with the final bound for DP.
-/

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

lemma reindex (α β : Type) (l v : List α) (b : List β) (h1 : l.length = v.length) (h2 : l.length = b.length)
  (f : α -> β -> ENNReal):
  ∏ (i : Fin l.length), f l[i] b[i] = ∏ (i : Fin v.length), f l[i] b[i] := by
   apply Fintype.prod_equiv (finCongr h1)
   intro x
   rfl

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
    rw [@sub_eq_zero]
    have h1 : num / den  < (2⁻¹ : ℝ) := num_den_simper num den h
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

lemma RRSamplePushForward_final_bound (num : Nat) (den : PNat) (h : 2 * num < den) (a a' : Bool) (b : Bool):
  RRSinglePushForward num den h a b / RRSinglePushForward num den h a' b
  ≤ (den + 2 * num) / (den - 2 * num) := by
  rw [← RRSingleSample_is_RRSinglePushForward num den h]
  apply final_bound

end RAPPOR
