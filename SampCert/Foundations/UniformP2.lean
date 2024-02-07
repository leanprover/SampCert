import SampCert.Foundations.Random
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Nat.Log

open Pmf Nat

-- Assumption: the Dafny version indeed has this spec
noncomputable def UniformPowerOfTwoSample (n : PNat) : RandomM Nat :=
  uniformOfFintype (Fin (2 ^ (log 2 n)))

@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) :
  x ∈ (UniformPowerOfTwoSample n).support →
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  intro SUPPORT
  simp only [UniformPowerOfTwoSample, Lean.Internal.coeM, Bind.bind, Pure.pure, bind_apply, uniformOfFintype_apply,
    Fintype.card_fin, cast_pow, cast_ofNat, pure_apply, one_div]
  simp only [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeOut.coe]
  -- have k : ENNReal := ((2 ^ log 2 ↑n)⁻¹)
  -- have HYP : Summable (fun a => if x = ↑a then 1 else 0) := sorry
  -- have H := tsum_const_smul' k
  -- rw [tsum_const_smul' k]
  -- rw [tsum_fintype]
  sorry

@[simp]
theorem UniformPowerOfTwoSample_double_apply (n : PNat) (x : Nat) :
  --x ∈ (UniformPowerOfTwoSample (2 * n)).support →
  (UniformPowerOfTwoSample (2 * n)) x = 1 / n := sorry
