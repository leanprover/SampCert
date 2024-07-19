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
  size : ℕ
  deriving Repr, DecidableEq

def IntHistogram.index (hist : IntHistogram) (i : ℤ) : ℤ := Id.run do
  if i - hist.min < 0 then
    panic "IntHistogram.get!: index lower than min"
  i + hist.min

def histToSTring (hist : IntHistogram) : String  := Id.run do
  let mut str := ""
  for i in [:hist.repr.size] do
    str := str ++ s!"({hist.index i},{hist.repr.get! i})  "
  return str

instance : ToString IntHistogram where
  toString := histToSTring



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

/--
  compute histogram of `samples`
-/
def histogram (samples : Array ℤ) (min max : ℤ) : IO IntHistogram := do
  if max < min then
    panic "histogram: max less than min"
  let mut hist : Array ℕ := mkArray (1 + max - min).toNat 0
  for v in samples do
    let idx := v - min
    if idx < 0 then
      panic "histogram: index less than 0"
    hist := hist.set! idx.toNat (hist.get! idx.toNat + 1)
  return { repr := hist, min := min, size := samples.size }

def estimateMean (hist : IntHistogram) : IO Float := do
  let mut acc : Float := 0
  for i in [:hist.repr.size] do
    acc := acc + Float.ofInt (hist.repr.get! i) * Float.ofInt (hist.index i)
  return acc / (hist.size).toFloat

def estimateVariance (hist : IntHistogram) (mean : Float) : IO Float := do
  let mut acc : Float := 0
  for i in [:hist.repr.size] do
    for _ in [:hist.repr.get! i] do
      acc := acc + (Float.ofInt (hist.index i) - mean)^2
  return acc / ((hist.size).toFloat - 1)

/--
  Not ideal to reuse IntHistogram for the CDF
-/
def estimateCDF (hist : IntHistogram) : IO IntHistogram := do
  IO.println s!"{hist}"
  if hist.size = 0 then
    panic "estimateCDF: empty histogram"
  let mut cdf : Array ℕ := mkArray hist.repr.size 0
  cdf := cdf.set! 0 <| hist.repr.get! 0
  for i in [1:cdf.size] do
    cdf := cdf.set! i <| cdf.get! (i - 1) + hist.repr.get! i
  return { repr := cdf, min := hist.min, size := hist.size }

def main : IO Unit := do
  let (samples, min, max) ← sample (DiscreteGaussianSample 1 1 7) 10000
  let hist ← histogram samples min max
  let mean ← estimateMean hist
  let variance ← estimateVariance hist mean
  let cdf ← estimateCDF hist
  IO.println s!"{mean} {variance}\n{hist}\n{cdf}"
