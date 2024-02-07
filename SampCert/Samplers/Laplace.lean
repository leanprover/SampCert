import SampCert.Foundations.Distributions
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential

open Pmf Nat

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : PNat) : RandomM (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) (K : Bool × PNat) : RandomM (Bool × PNat) := do
  let A ← BernoulliExpNegSampleUnit num den
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : RandomM (Bool × Nat) := do
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Nat × Bool => x.2) sorry
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × PNat => K.1) (DiscreteLaplaceSampleLoopIn2 1 1) sorry (true,1)
  let V := r2.2 - 2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : PNat) : RandomM Int := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0)) sorry
  let Z : Int := if r.1 then - r.2 else r.2
  return Z
