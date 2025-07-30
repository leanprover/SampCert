import SampCert.Util.Log
import Mathlib.Topology.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

lemma numerator_pos (num : ℕ) (den : ℕ+) : (0 : ℝ) < ↑↑den + 2 * num := by
  have den_pos : 0 < (den : ℕ) := den.property
  have den_real_pos : (0 : ℝ) < ↑(den : ℕ) := Nat.cast_pos.mpr den_pos
  have two_num_nonneg : 0 ≤ (2 * num : ℝ) := by
    refine mul_nonneg ?_ (Nat.cast_nonneg num)
    norm_num
  exact add_pos_of_pos_of_nonneg den_real_pos two_num_nonneg

lemma denominator_pos (num : ℕ) (den : PNat) (h : 2 * num < den) : (0 : ℝ) < ↑↑den - 2 * ↑num := by
  simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, sub_pos]
  norm_cast
  exact Nat.cast_lt.mpr h


lemma step1 (num : Nat) (den : PNat) (h : 2 * num < den):
ENNReal.ofReal ((den + 2 * num) / (den - 2 * num)) = ENNReal.ofReal (Real.exp (Real.log ((den + 2 * num) / (den - 2 * num)))) := by
  congr
  rw [eq_comm]
  apply Real.exp_log
  apply div_pos
  {exact numerator_pos num den}
  {exact denominator_pos num den h}

lemma step2 (num : Nat) (den : PNat) (h : 2 * num < den):
    (↑↑den + 2 * ↑num) / (↑↑den - 2 * ↑num) = ENNReal.ofReal ((↑↑den + 2 * ↑num) / (↑↑den - 2 * ↑num)) := by
  rw [ENNReal.ofReal_div_of_pos]
  · sorry


  · have foo : 2 * (num : ℝ) < (den : ℕ) := by exact_mod_cast h
    exact sub_pos.mpr foo

lemma final_step_combined (num : Nat) (den : PNat) (h : 2 * num < den) :
(den + (2: ENNReal) * num) / (den - (2 : ENNReal) * num) = ENNReal.ofReal (Real.exp (Real.log ((den + 2 * num) / (den - 2 * num)))) := by
  rw [← step1 num den h]
  exact step2 num den h

lemma reduce (num : Nat) (den : PNat):
((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num): ℝ) = (1 / 2 + ↑num / ↑(NNReal.ofPNat den)) / (1 / 2 - ↑num / ↑(NNReal.ofPNat den)) := by
  simp
  rw [inv_eq_one_div]
  rw [div_add_div]
  · rw [one_mul]
    rw [div_sub_div]
    rw [one_mul]
    rw [div_div_div_eq]
    nth_rewrite 2 [div_eq_mul_inv]
    nth_rewrite 4 [mul_comm]
    rw [← div_eq_mul_inv]
    rw [mul_div_mul_left]
    apply ne_of_gt
    simp_all only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, NNReal.coe_pos, Nat.cast_pos]
    exact den.2
    aesop
    apply ne_of_gt
    simp_all only [NNReal.coe_pos, Nat.cast_pos]
    exact den.2
  · aesop
  · apply ne_of_gt
    simp_all only [NNReal.coe_pos, Nat.cast_pos]
    exact den.2



lemma final_coercion (num : Nat) (den : PNat) (h : 2 * num < den):
(↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num) ≤
  ENNReal.ofReal (Real.exp (Real.log ((1 / 2 + ↑num / ↑(NNReal.ofPNat den)) / (1 / 2 - ↑num / ↑(NNReal.ofPNat den))))):= by
  rw [final_step_combined num den h]
  rw [reduce num den]
