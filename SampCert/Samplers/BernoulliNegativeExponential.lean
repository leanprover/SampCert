/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli

open PMF Nat

noncomputable def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (state : (Bool × PNat)) : RandomM (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den)
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) : RandomM Bool := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den) sorry (true,1)
  let K : Nat := r.2
  if K % 2 = 0 then return true else return false

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1
    let R ← BernoulliExpNegSampleGenLoop (iter - 1)
    return (B ∧ R)

noncomputable def BernoulliExpNegSample (num : Nat) (den : PNat) : RandomM Bool := do
  if num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den
       return X
  else
    let gamf := floor (num / den)
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
         let num := num - gamf * den
         let X ← BernoulliExpNegSampleUnit num den
         return X
    else return false
