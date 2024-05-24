/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code

/-!
# Discrete Laplace Sampler

This file implements a sampler for the discrete laplace distribution.

## Implementation notes

MARKUSDE: cite?

-/

noncomputable section

namespace SLang

def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : SLang (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

def DiscreteLaplaceSampleLoopIn1 (t : PNat) : SLang Nat := do
  let r1 ← probUntil (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
  return r1.1

-- Note that for the arxiv algorithm, we can call Unit directly
def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)  (K : Bool × Nat) : SLang (Bool × Nat) := do
  let A ← BernoulliExpNegSample num den
  return (A, K.2 + 1)

def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : SLang Nat := do
  let r2 ← probWhile (λ K : Bool × Nat => K.1) (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
  return r2.2

-- We need to generate and test both implementations
def DiscreteLaplaceSampleLoop' (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let U ← DiscreteLaplaceSampleLoopIn1 num
  let v ← DiscreteLaplaceSampleLoopIn2 1 1
  let V := v - 1 -- MARKUSDE ???
  let X := U + num * V
  let Y := X / den
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,Y)

-- MARKUSDE: Why can we throw away the ``U`` term?
def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let v ← DiscreteLaplaceSampleLoopIn2 den num
  let V := v - 1
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,V)

/--
``SLang`` term to obtain a sample from the discrete Laplace distribution
-/
def DiscreteLaplaceSample (num den : PNat) : SLang ℤ := do
  let r ← probUntil (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

end SLang
