/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector.Basic

/-!
# ``privParNoisedHistogram`` Implementation

This file implements a histogram with noised bins, computed in parallel
-/


namespace SLang

variable [dps : DPPar T]
variable [dpn : DPNoise dps.toDPSystem]

variable (numBins : ℕ+)
variable (B : Bins T numBins)


def privParNoisedBinCount (ε₁ ε₂ : ℕ+) (b : Fin numBins) : Mechanism T ℤ :=
  (dpn.noise (exactBinCount numBins B b) 1 ε₁ ε₂)

def privParNoisedHistogramAux (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) : Mechanism T (Histogram T numBins B) :=
  let privParNoisedHistogramAux_rec :=
    match n with
    | Nat.zero => privConst (emptyHistogram numBins B)
    | Nat.succ n' => privParNoisedHistogramAux ε₁ ε₂ n' (Nat.lt_of_succ_lt Hn)
  privPostProcess
    (privParCompose
      (privParNoisedBinCount numBins B ε₁ ε₂ ⟨n, Hn⟩)
      privParNoisedHistogramAux_rec
      (B.bin · = ⟨n, Hn⟩))
    (fun z => setCount numBins B z.2 ⟨n, Hn⟩ z.1)

/--
Histogram with noise added to each count
-/
def privParNoisedHistogram (ε₁ ε₂ : ℕ+) : Mechanism T (Histogram T numBins B) :=
  privParNoisedHistogramAux numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins)

end SLang
