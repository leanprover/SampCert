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

theorem halve_wf (num : Nat) (den st : PNat) (wf : num ≤ den) :
  num ≤ ↑(st * den) := by
  simp
  cases st
  rename_i v p
  simp
  exact le_mul_of_one_le_of_le p wf

noncomputable def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : RandomM (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Nat := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
  return r.2

@[simp]
theorem BernoulliExpNegSampleUnitAux_zero (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) 0 st st' = 0 := by
  simp [prob_while_cut]

@[simp]
theorem BernoulliExpNegSampleUnitAux_returns_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (true, r) = 0 := by
  revert st r
  induction fuel
  . simp [prob_while_cut]
  . rename_i fuel IH
    intro st r
    simp [prob_while_cut, WhileFunctional]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [ite_apply]
    split
    . rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      conv =>
        left
        right
        intro a
        rw [IH a r]
      simp
    . rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_ite_simpl (x r : ℕ+) (k : ENNReal) :
  @ite ENNReal (x = r + 1) (Classical.propDecidable (x = r + 1)) 0
  (@ite ENNReal (x = r + 1) (instPNatDecidableEq x (r + 1)) k 0) = 0 := by
  split
  . simp
  . simp

theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st
    + (1 - (num / (r * den))) * prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st := by
  cases st
  rename_i b' r'
  simp [prob_while_cut, WhileFunctional, ite_apply, ENNReal.tsum_prod', tsum_bool, BernoulliExpNegSampleUnitLoop]
  conv =>
    left
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]
    . rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]



@[simp]
theorem BernoulliExpNegSampleUnitAux_apply (num : Nat) (den : PNat) (wf : num ≤ den) (n : Nat) (gam : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
  ENNReal.ofReal ((γ^(n - 1) / (factorial (n - 1))) - (γ^n / (factorial n))) := by
  simp [BernoulliExpNegSampleUnitAux, prob_while]
  unfold BernoulliExpNegSampleUnitLoop
  simp
  unfold SubPMF.bind
  unfold SubPMF.pure
  simp
  sorry

noncomputable def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

@[simp]
theorem BernoulliExpNegSampleUnit_apply_false (num : Nat) (den : PNat)  (wf : num ≤ den) (gam : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSampleUnit num den wf) false = ENNReal.ofReal (Real.exp (- γ)) := by
  have B : Real.exp (-γ) ≥ 0 := by exact Real.exp_nonneg (-γ)
  simp [BernoulliExpNegSampleUnit]
  unfold SubPMF.pure
  simp [ite_apply]
  conv =>
    left
    right
    intro a
    rw [BernoulliExpNegSampleUnitAux_apply num den wf a gam]
  have C : (∑' (a : ℕ), if a % 2 = 0 then 0 else ENNReal.ofReal (γ ^ (a - 1) / ↑(a - 1)! - γ ^ a / ↑a !))
    = (∑' (a : ℕ), ENNReal.ofReal ((-γ)^a / (a - 1)!)) := by sorry
  rw [C]
  sorry -- need to connect to definition of exp

@[simp]
theorem BernoulliExpNegSampleUnit_apply_true (num : Nat) (den : PNat)  (wf : num ≤ den) (gam : γ = (num : ℝ) / (den : ℝ)) :
  (BernoulliExpNegSampleUnit num den wf) true = 1 - ENNReal.ofReal (Real.exp (- γ)) := by
  sorry

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    if ¬ B then return B else
      let R ← BernoulliExpNegSampleGenLoop (iter - 1)
      return R

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
