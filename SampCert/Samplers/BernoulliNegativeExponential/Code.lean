/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang
import SampCert.Samplers.Bernoulli.Code

noncomputable section

namespace SLang

theorem halve_wf (num : Nat) (den st : PNat) (wf : num ≤ den) :
  num ≤ ↑(st * den) := by
  simp
  cases st
  rename_i v p
  simp
  exact le_mul_of_one_le_of_le p wf

def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : SLang (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
  return (A, state.2 + 1)

def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Nat := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
  return r.2

def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

def BernoulliExpNegSampleGenLoop (iter : Nat) : SLang Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    if ¬ B then return B else
      let R ← BernoulliExpNegSampleGenLoop (iter - 1)
      return R

theorem rat_less_floor_le1 (num : Nat) (den : PNat) :
  (num % den) ≤ den := by
  have A := Nat.mod_lt num (PNat.pos den)
  exact Nat.lt_succ.mp (Nat.le.step A)

def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := do
  if h : num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h
       return X
  else
    let gamf := num / den
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
      let X ← BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)
      return X
    else return false

end SLang
