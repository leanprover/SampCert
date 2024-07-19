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

/--
  Moment estimate, unadjusted
-/
def estimateMoment (hist : IntHistogram) (mean : Float) (moment : ℕ) : IO Float := do
  if moment < 2 then
    panic "estimateMoment: moment must be at least 2"
  let mut acc : Float := 0
  for i in [:hist.repr.size] do
    for _ in [:hist.repr.get! i] do
      acc := acc + (Float.ofInt (hist.index i) - mean)^moment.toFloat
  return acc / (hist.size).toFloat

def estimateVariance (hist : IntHistogram) (mean : Float) : IO Float := do
  estimateMoment hist mean 2

def estimateSkewness (hist : IntHistogram) (mean : Float) (variance : Float) : IO Float := do
  let μ₃ ← estimateMoment hist mean 3
  return μ₃ / (variance^(1.5))

def estimateKurtosis (hist : IntHistogram) (mean : Float) (variance : Float) : IO Float := do
  let μ₃ ← estimateMoment hist mean 4
  return μ₃ / (variance^2)

/--
  Not ideal to reuse IntHistogram for the CDF
  Warning: unnormalized
-/
def estimateCDF (hist : IntHistogram) : IO IntHistogram := do
  if hist.size = 0 then
    panic "estimateCDF: empty histogram"
  let mut cdf : Array ℕ := mkArray hist.repr.size 0
  cdf := cdf.set! 0 <| hist.repr.get! 0
  for i in [1:cdf.size] do
    cdf := cdf.set! i <| cdf.get! (i - 1) + hist.repr.get! i
  return { repr := cdf, min := hist.min, size := hist.size }

def evalUnnormalizedGaussianPDF (x : ℤ) (num den : ℕ+) : IO Float := do
  return Float.exp <| (- (Float.ofInt x)^2) / (2 * ((num : ℕ).toFloat^2 / (den : ℕ).toFloat^2))

def sumTo (bound : ℤ) (tob : ℤ) (num den : ℕ+) : IO Float := do
  let mut acc : Float := 0
  let dist := Int.natAbs (tob - bound)
  for x in [:dist + 1] do
    let mass ← evalUnnormalizedGaussianPDF (x + bound) num den
    acc := acc + mass
  return acc

def approxNormalizerGaussianPDF (num den : ℕ+) (bound : ℤ) : IO Float := do
  sumTo (-bound) bound num den

def KolmogorovDistance (hist : IntHistogram) (num den : ℕ+) : IO Float := do
  let mut max : Float := 0
  let bound : ℕ := 50 * num^2 -- We should do better when Init has rationals
  let norm : Float ← approxNormalizerGaussianPDF num den bound
  for i in [:hist.repr.size] do
    let sample := hist.index i
    let refCDFUnnormed ← sumTo (- bound) sample num den
    let refCDF := refCDFUnnormed / norm
    let estCDF : Float := (Float.ofNat (hist.repr.get! i)) / (Float.ofInt hist.size)
    let d := (refCDF - estCDF).abs
    if max < d then
      max := d
  return max

def main : IO Unit := do
  let num : ℕ+ := 1
  let den : ℕ+ := 1
  let (samples, min, max) ← sample (DiscreteGaussianSample num den 7) 10000
  let hist ← histogram samples min max
  let mean ← estimateMean hist
  let variance ← estimateVariance hist mean
  let skewness ← estimateSkewness hist mean variance
  let kurtosis ← estimateSkewness hist mean variance
  let cdf ← estimateCDF hist
  let D ← KolmogorovDistance cdf num den
  IO.println s!"{mean} {variance} {skewness} {kurtosis} {D}\n {cdf}"
