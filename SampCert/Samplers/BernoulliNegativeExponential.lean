/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import Mathlib.Data.Complex.Exponential

open PMF Nat

noncomputable def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : RandomM (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) sorry
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Nat := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) sorry (true,1)
  return r.2

@[simp]
theorem BernoulliExpNegSampleUnitAux_apply (num : Nat) (den : PNat) (wf : num ≤ den) (n : Nat) (_ : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
  ENNReal.ofReal ((γ^(n - 1) / (factorial (n - 1))) - (γ^n / (factorial n))) := sorry

noncomputable def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

@[simp]
theorem BernoulliExpNegSampleUnit_apply (num : Nat) (den : PNat)  (wf : num ≤ den) (_ : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSampleUnit num den wf) true = ENNReal.ofReal (Real.exp (-γ)) := sorry

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    let R ← BernoulliExpNegSampleGenLoop (iter - 1)
    return (B ∧ R)

noncomputable def BernoulliExpNegSample (num : Nat) (den : PNat) : RandomM Bool := do
  if h : num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h
       return X
  else
    let gamf := floor (num / den)
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
         let num := num - gamf * den
         let X ← BernoulliExpNegSampleUnit num den sorry
         return X
    else return false

@[simp]
theorem BernoulliExpNegSample_apply (num : Nat) (den : PNat) (_ : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSample num den) true = ENNReal.ofReal (Real.exp (-γ)) := sorry
