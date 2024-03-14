/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import Mathlib.Data.Complex.Exponential

open PMF Nat BigOperators Finset

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

@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (true, r + 1) st
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
  simp
  rw [add_comm]


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (false, r) st =
  if st = (false,r) then 1 else 0 := by
  cases st
  simp [prob_while_cut, WhileFunctional]

@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_counter (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  . simp
  . rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    . simp
      exact Ne.symm (h1 rfl)
    . simp [BernoulliExpNegSampleUnitAux_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact eq_or_lt_of_le h2
        cases OR
        . rename_i h
          subst h
          exact _root_.ne_of_gt le.refl
        . rename_i h
          exact _root_.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by exact
        (bne_iff_ne (true, stn + 1) (false, n)).mp rfl
      rw [IH _ A]
      rw [IH _ B]
      simp
      exact le.step h2
      exact le.step h2

-- Used to explore
example (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf)
    2 (true, 1) (false,⟨ 3, sorry ⟩) = 1 := by
  simp [prob_while_cut, WhileFunctional, BernoulliExpNegSampleUnitLoop, ite_apply, ENNReal.tsum_prod', tsum_bool]
  sorry

example :
  (2 : ℕ+) + (1 : ℕ) = (3 : ℕ+) := by
  exact rfl

def plus_one (k : ℕ) : ℕ+ := ⟨ k + 1 , Nat.add_pos_right k le.refl ⟩

theorem plus_one_prop (k : ℕ) :
  plus_one k = k + 1 := by
  simp [plus_one]

def plus_two (k fuel : ℕ) : ℕ+ := ⟨ fuel + k + 2 , Nat.add_pos_right (fuel + k) (le.step le.refl) ⟩

theorem plus_two_zero_prop (k : ℕ) :
  plus_two k 0 = k + 2 := by
  simp [plus_two]

-- Warning! BernoulliExpNegSampleUnitAux has a transition phase
@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_progress (num : ℕ) (den : ℕ+) (fuel k : ℕ) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel ) = (∏ i in range (min (fuel + 2) (fuel + k + 1) - 2), num / (den * (k + i))) * (1 - (num / ((fuel + k + 1) * den))) := by
  revert k
  induction fuel
  . intro k
    simp
    split
    . rename_i h
      rw [plus_one_prop]
      simp
    . rename_i h
      have A : ¬ k + 2 = k + 2 := by
        conv =>
          right
          congr
          . rw [← plus_two_zero_prop]
          . change k + (1 + 1)
            rw [← add_assoc]
            rw [← plus_one_prop]
        refine (Function.Injective.ne_iff ?hf).mpr h
        exact PNat.coe_injective
      contradiction
  . rename_i fuel IH
    intro k
    rw [BernoulliExpNegSampleUnitAux_succ_true]
    rw [BernoulliExpNegSampleUnitAux_succ_false]
    -- Second term is 0
    have IH' := IH (k + 1)
    clear IH
    sorry

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
