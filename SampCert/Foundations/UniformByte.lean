/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Util.Util
import SampCert.Foundations.Auto
import SampCert.Foundations.UniformP2

/-!
# ``probUniformByte`` Properties

This file contains lemmas about ``probUniformByte``, a ``SLang`` sampler for the
uniform distribution on bytes.

It also contains the derivation that ``probUniformP2`` is a uniform distribution.
-/


open Classical Nat PMF

namespace SLang

/--
ProbUniformByte is a proper distribution
-/
def probUniformByte_normalizes : HasSum probUniformByte 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold SLang.probUniformByte
  rw [division_def]
  rw [ENNReal.tsum_mul_right]
  simp only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_one_iff _).mp
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.tsum_toReal_eq ?G1]
  case G1 => simp
  simp only [ENNReal.one_toReal, tsum_const, nsmul_eq_mul, mul_one]
  rw [@Nat.card_eq_of_equiv_fin UInt8 256 ?G1]
  case G1 =>
    apply Equiv.ofBijective (fun v => v.val)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => {val := v : UInt8})
    simp [Function.RightInverse, Function.LeftInverse]
  simp [ENNReal.toReal_inv]

/--
ProbUniformByte as a PMF
-/
def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

-- Might not be used

-- /-
-- Evaluation of ``probUniformByteUpperBits`` for zero-shifts inside the support
-- -/
-- def probUniformByteUpperBits_eval_overshift_support {i x : ℕ} (Hi : 8 ≤ i) (Hx : x < UInt8.size) :
--     probUniformByteUpperBits i x = 1 / UInt8.size := sorry
--
-- /-
-- Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-- -/
-- def probUniformByteUpperBits_eval_overshift_nil {i x : ℕ} (Hi : 8 ≤ i) (Hx : x ≥ UInt8.size) :
--     probUniformByteUpperBits i x = 0 := sorry


/--
Evaluation of ``probUniformByteUpperBits`` for inside the support
-/
def probUniformByteUpperBits_eval_support {i x : ℕ} (Hx : x < 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 2^(8 - i) / UInt8.size := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]

  -- Nat.shiftRight_eq_div_pow
  sorry

/--
Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-/
def probUniformByteUpperBits_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 0 := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]
  intro v H1
  exfalso
  cases (Classical.em (i < 8))
  · -- i < 8
    rename_i Hi
    rw [max_eq_left (by linarith)] at H1
    rw [min_eq_right (by linarith)] at Hx
    simp_all
    rw [Nat.shiftRight_eq_div_pow] at *
    have H2 := UInt8.toNat_lt v
    apply Nat.mul_le_of_le_div (2 ^ (8 - i)) (2 ^ i) v.toNat at Hx
    rw [<- pow_add] at Hx
    have X : (i + (8 - i)) = 8 := by
      apply add_sub_of_le
      linarith
    rw [X] at Hx
    clear X
    linarith
  · -- i >= 8
    rename_i Hi
    rw [max_eq_right (by linarith)] at H1
    rw [min_eq_left (by linarith)] at Hx
    have H2 := UInt8.toNat_lt v
    simp_all
    linarith

/--
Evaluation of ``probUniformP2`` for inside the support
-/
def probUniformP2_eval_support {i x : ℕ} (Hx : x < 2 ^ i):
    probUniformP2 i x = (1 / 2 ^ i) := by
  sorry
-- Want: strong induction. How to do in Lean?

/--
Evaluation of ``probUniformP2`` for zero-shifts outside of the support
-/
def probUniformP2_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ i):
    probUniformP2 i x = 0 := by
  sorry


/--
Evaluates the ``probUniformP2`` distribution at a point inside of its support.
-/
@[simp]
theorem UniformPowerOfTwoSample'_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
    UniformPowerOfTwoSample' n x = 1 / (2 ^ (log 2 n)) := by
  rw [UniformPowerOfTwoSample']
  rw [probUniformP2_eval_support h]

/--
Evaluates the ``probUniformP2`` distribution at a point outside of its support
-/
@[simp]
theorem UniformPowerOfTwoSample'_apply' (n : PNat) (x : Nat) (h : x ≥ 2 ^ (log 2 n)) :
    UniformPowerOfTwoSample' n x = 0 := by
  rw [UniformPowerOfTwoSample']
  apply probUniformP2_eval_zero
  linarith

/--
Equivalence between uniform samplers
-/
def probUniform_probUniform'_equiv (n : ℕ+) : UniformPowerOfTwoSample n = UniformPowerOfTwoSample' n := by
  apply SLang.ext
  intro x
  cases (Classical.em (x < 2 ^ (log 2 n)))
  · rename_i h
    rw [UniformPowerOfTwoSample_apply n x h]
    rw [← UniformPowerOfTwoSample'_apply n x h]
  · rename_i h'
    have h : x ≥ 2 ^ (log 2 n) := by linarith
    rw [UniformPowerOfTwoSample_apply' n x h]
    rw [← UniformPowerOfTwoSample'_apply' n x h]

end SLang
