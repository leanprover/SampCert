/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential

open PMF Nat Real

noncomputable def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : RandomM (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : PNat) : RandomM Nat := do
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
  return r1.1

theorem DiscreteLaplaceSampleLoopIn1_apply (t : PNat) (n : ℕ) :
  (DiscreteLaplaceSampleLoopIn1 t) n = 42 := by
  simp [DiscreteLaplaceSampleLoopIn1, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp [tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  have A : ∀ x : ℕ, @ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
          (DiscreteLaplaceSampleLoopIn1Aux t (x, true) *
          (1 - ∑' (i : { x : Nat × Bool // x.2 = false }), DiscreteLaplaceSampleLoopIn1Aux t ↑i)⁻¹ *
          @ite ENNReal (n = x) (Classical.propDecidable (n = (x, true).1)) 1 0) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h h'
        subst h'
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  simp
  simp [DiscreteLaplaceSampleLoopIn1Aux, tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  clear A
  have A : ∀ x : ℕ, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
            (@ite ENNReal (n = x) (instDecidableEqNat n x) (UniformSample t x * BernoulliExpNegSample x t true) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h h'
        subst h'
        contradiction
      . simp
  conv =>
    left
    left
    right
    right
    intro x
    rw [A]
  clear A
  simp
  rw [uniformSample_apply']
  rw [BernoulliExpNegSample_apply_true n t rfl]
  rw [ENNReal.tsum_comm]
  rw [← ENNReal.tsum_geometric]
  conv =>
    left
    right
    right
    intro n
    left
    right
    intro b
    rw [ENNReal.tsum_mul_left]
  simp
  sorry

noncomputable def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat) (wf : num ≤ den) (K : Bool × PNat) : RandomM (Bool × PNat) := do
  let A ← BernoulliExpNegSampleUnit num den wf
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : RandomM PNat := do
  let r2 ← prob_while (λ K : Bool × PNat => K.1) (DiscreteLaplaceSampleLoopIn2Aux 1 1 (le_refl 1)) (true,1)
  return r2.2

noncomputable def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : RandomM (Bool × Nat) := do
  let U ← DiscreteLaplaceSampleLoopIn1 num
  let v ← DiscreteLaplaceSampleLoopIn2 1 1
  let V := v - 2
  let X := U + num * V
  let Y := X / den
  let B ← BernoulliSample 1 2 sorry
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : PNat) : RandomM ℤ := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

@[simp]
theorem DiscreteLaplaceSample_apply (num den : PNat) (x : ℤ) (_ : t = (num : ℝ) / (den : ℝ)) :
  (DiscreteLaplaceSample num den) x = ENNReal.ofReal (((exp (1/t) - 1) / (exp (1/t) + 1)) * (exp (- (abs x / t)))) := sorry
