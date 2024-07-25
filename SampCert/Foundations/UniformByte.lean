/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Util.Util
import SampCert.Foundations.Auto

/-!
# ``probUniformByte`` Properties

This file contains lemmas about ``probUniformByte``, a ``SLang`` sampler for the
uniform distribution on bytes.
-/


open Classical Nat PMF

namespace SLang

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

def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

end SLang
