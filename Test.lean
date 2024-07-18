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

open SLang Std

def sample (dist : SLang ℤ) (numSamples : ℕ) : IO (List ℤ) := do
  let mut samples : List ℤ := []
  for _ in [:numSamples] do
    let s : ℤ ← run <| dist
    samples := s :: samples
  return samples

def estimateMean (samples : List ℤ) : IO Float := do
  let mut acc : Float := 0
  for s in samples do
    acc := acc + Float.ofInt s
  return acc / (samples.length).toFloat

def estimateVariance (samples : List ℤ) (mean : Float) : IO Float := do
  let mut acc : Float := 0
  for s in samples do
    acc := acc + (Float.ofInt s - mean)^2
  return acc / ((samples.length).toFloat - 1)

def main : IO Unit := do
  let samples ← sample (DiscreteGaussianSample 1 1 7) 1000000
  let mean ← estimateMean samples
  let variance ← estimateVariance samples mean
  IO.println s!"{mean} {variance}"
