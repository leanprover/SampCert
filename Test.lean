/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Bernoulli.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code
import SampCert.Samplers.LaplaceGen.Code
import SampCert.Samplers.Geometric.Code
import SampCert.Samplers.Gaussian.Code
import SampCert.Samplers.GaussianGen.Code

open SLang Std Int Array

structure IntHistogram where
  repr : Array ℕ
  min : ℤ

/--
  sample `numSamples` times from `dist` into an array and keep track
  of the minimum and maximum sample value
-/
def sample (dist : SLang ℤ) (numSamples : ℕ) : IO ((Array ℤ) × ℤ × ℤ) := do
  if numSamples < 2 then
    panic "sample: 2 samples at least required"
  let mut samples : Array ℤ := mkArray numSamples 0
  let s₁ : ℤ ← run <| dist
  samples := samples.set! 0 s₁
  let s₂ : ℤ ← run <| dist
  samples := samples.set! 1 s₂
  let mut min : ℤ := s₁
  let mut max : ℤ := s₂
  if s₂ < s₁ then
    min := s₂
    max := s₁
  for i in [2:numSamples] do
    let s : ℤ ← run <| dist
    samples := samples.set! i s
    if s < min then
      min := s
    else if s > max then
      max := s
  return (samples,min,max)

def estimateMean (samples : Array ℤ) : Float := Id.run do
  let mut acc : Float := 0
  for s in samples do
    acc := acc + Float.ofInt s
  return acc / (samples.size).toFloat

def estimateVariance (samples : Array ℤ) (mean : Float) : Float := Id.run do
  let mut acc : Float := 0
  for s in samples do
    acc := acc + (Float.ofInt s - mean)^2
  return acc / ((samples.size).toFloat - 1)

instance : DecidableRel Int.le := by
  simp [DecidableRel]
  intros a b
  apply Int.decLe

/--
  compute histogram of `samples`
-/
def histogram (samples : Array ℤ) (min max : ℤ) : IntHistogram :=  Id.run do
  if max < min then
    panic "histogram: max less than min"
  let mut hist : Array ℕ := mkArray (1 + max - min).toNat 0
  for v in samples do
    let idx := v - min
    if idx < 0 then
      panic "histogram: index less than 0"
    hist := hist.set! idx.toNat (hist.get! idx.toNat + 1)
  return { repr := hist, min := min }

def main : IO Unit := do
  let (samples, min, max) ← sample (DiscreteGaussianSample 1 1 7) 10000
  let mean := estimateMean samples
  let variance := estimateVariance samples mean
  let hist := histogram samples min max
  IO.println s!"{mean} {variance} {hist.repr.size}"
