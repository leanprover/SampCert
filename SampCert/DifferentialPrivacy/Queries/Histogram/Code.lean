/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector.Basic

/-!
# ``privHistogram`` Implementation

This file implements a logarithmic histogram with noised bins
-/

/--
Function to categorize values of type T into ``num_bins.succ`` distinct bins.
-/
structure Bins (T : Type) (num_bins : ℕ) where
  bin : T -> Fin num_bins


/-!
## Private Histograms
-/

noncomputable section

variable (numBins : ℕ+)

def predBins : ℕ := numBins.natPred

def predBins_lt_numBins : predBins numBins < numBins := by
  rw [predBins]
  cases numBins
  rename_i v Hv
  simp
  sorry
  -- apply Nat.sub_one_lt_of_le Hv
  -- exact Nat.le_refl v


/--
A histogram with a fixed binning method and ``i+1`` bins

Counts in the histogram are permitted to be negative.
-/
structure Histogram (T : Type) (num_bins : ℕ+) (B : Bins T num_bins) where
  count : Vector ℤ num_bins

variable {T : Type}
variable (B : Bins T numBins)

/--
Construct an empty histagram
-/
def emptyHistogram : Histogram T numBins B :=
  Histogram.mk (Vector.replicate numBins 0)

-- Is there any way to get the discrete measure space for free?
instance : MeasurableSpace (Histogram T numBins B) where
  MeasurableSet' _ := True
  measurableSet_empty := by simp
  measurableSet_compl := by simp
  measurableSet_iUnion := by simp

-- There's probably an easier way to do this?
instance : Countable (Histogram T numBins B) where
  exists_injective_nat' := by
    have X : Countable (Vector ℤ numBins) := by
      sorry
    have Y : ∃ f : Vector ℤ numBins -> ℕ, Function.Injective f := by
      sorry
    sorry

instance : Inhabited (Histogram T numBins B) where
  default := emptyHistogram numBins B

instance : DiscreteMeasurableSpace (Histogram T numBins B) where
  forall_measurableSet := by simp

namespace SLang

variable [dps : DPSystem T]

/--
Compute the exact number of elements inside a histogram bin
-/
def exactBinCount (b : Fin numBins) (l : List T) : ℤ :=
  List.length (List.filter (fun v => B.bin v = b) l)

/--
Compute a noised count of the number of list elements inside a particular histogram bin
-/
def privNoisedBinCount (ε₁ ε₂ : ℕ+) (b : Fin numBins) : Mechanism T ℤ :=
  (dps.noise (exactBinCount numBins B b) 1 ε₁ (ε₂ * numBins))

/--
Modify a count inside a Histogram
-/
def setCount (h : Histogram T numBins B) (b : Fin numBins) (v : ℤ) : Histogram T numBins B :=
  { h with count := h.count.set b v }

def privNoisedHistogramAux (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) : Mechanism T (Histogram T numBins B) :=
  let privNoisedHistogramAux_rec :=
    match n with
    | Nat.zero => privConst (emptyHistogram numBins B)
    | Nat.succ n' => privNoisedHistogramAux ε₁ ε₂ n' (Nat.lt_of_succ_lt Hn)
  privPostProcess
    (privCompose (privNoisedBinCount numBins B ε₁ ε₂ n) privNoisedHistogramAux_rec)
    (fun z => setCount numBins B z.2 n z.1)


/--
Histogram with noise added to each count
-/
def privNoisedHistogram (ε₁ ε₂ : ℕ+) : Mechanism T (Histogram T numBins B) :=
  privNoisedHistogramAux numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins)


/--
Compute the maximum bin above threshold
-/
def exactMaxBinAboveThresholdAux (τ : ℤ) (n : ℕ) (Hn : n < numBins) (h : Histogram T numBins B) : Option (Fin numBins) :=
  match n with
  | Nat.zero => none
  | Nat.succ n' =>
    let n_fin := (Fin.mk n'.succ Hn)
    if (h.count.get n_fin > τ)
      then some n_fin
      else exactMaxBinAboveThresholdAux τ n' (Nat.lt_of_succ_lt Hn) h

/--
Compute the noisy maximum histogram bin whose value exeeds τ
-/
def privMaxBinAboveThreshold (ε₁ ε₂ : ℕ+) (τ : ℤ) : Mechanism T (Option (Fin numBins)) :=
  privPostProcess
    (privNoisedHistogram numBins B ε₁ ε₂)
    (exactMaxBinAboveThresholdAux numBins B τ (predBins numBins) (predBins_lt_numBins numBins))

end SLang
