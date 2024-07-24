/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Queries.BoundedMean.Basic
import SampCert.DifferentialPrivacy.Queries.Histogram.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.System
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.HistogramMean.Properties
import SampCert.Samplers.Gaussian.Properties

open SLang PMF

def combineConcentrated := @privNoisedBoundedMean_DP gaussian_zCDPSystem
def combinePure := @privNoisedBoundedMean_DP PureDPSystem

/-
##  Example: execute the histogram mean on a list
-/
section histogramMeanExample

def numBins : ℕ+ := 64

/-
Bin the infinite type ℕ with clipping
-/
def bin (n : ℕ) : Fin numBins :=
  { val := min (Nat.log 2 n) (PNat.natPred numBins),
    isLt := by
      apply min_lt_iff.mpr
      right
      exact Nat.lt_of_sub_eq_succ rfl
  }

/-
Return an upper bound on the bin value, clipped to 2^(1 + numBins)
-/
def unbin (n : Fin numBins) : ℕ+ := 2 ^ (1 + n.val)

noncomputable def combineMeanHistogram : Mechanism ℕ (Option ℚ) :=
  privMeanHistogram PureDPSystem numBins { bin } unbin 1 20 2 1 20

end histogramMeanExample

-- The following is unsound and should NOT be part of the code
-- We are using it for now until the Python FFI is richer
@[extern "dirty_io_get"]
opaque DirtyIOGet(x : IO ℤ) : UInt32

@[export dgs_get]
def DiscreteGaussianSampleGet (num den : UInt32) (mix: UInt32) : UInt32 := Id.run do
  let z : IO ℤ ← run <| DiscreteGaussianPMF ⟨ num.toNat , sorry ⟩ ⟨ den.toNat , sorry ⟩ mix.toNat
  return DirtyIOGet z
