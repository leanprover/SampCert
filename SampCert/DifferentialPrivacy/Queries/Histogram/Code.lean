/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector

/-!
# ``privHistogram`` Implementation

This file implements a logarithmic histogram with noised bins
-/




/--
Minimum value of a Long type
-/
def LongMIN : ℤ := -2^63

/--
Maximum value of a Long type
-/
def LongMAX : ℤ := 2^63 - 1

/--
Long type: integers in the range [-2^63, 2^63-1] inclusive.
-/
def Long : Type := { x : ℤ | LongMIN <= x ∧ x <= LongMAX }


/--
Function to categorize values of type T into ``i.succ`` distinct bins.
-/
structure Bins (T : Type) (num_bins : ℕ) where
  bin : T -> Fin num_bins

-- This function is extracted already
-- #check Nat.log 2
/-
-- Try to replicate the formula to get even(ish) bins
-- Nonnegative bins: [0, 1], (1, 2], (2, 4], ...
-- Negative bins: ..., [-4, -2), [-2, -1), [-1]

def neg_f (z : ℤ) : ℕ := 62 - Nat.log 2 (Int.toNat (-z - 1))
def pos_f (z : ℤ) : ℕ := Nat.log 2 (Int.toNat z - 1) + 64
def zer_f (z : ℤ) : ℕ := 63

-- [-2^63, -2^62)
#eval neg_f (-2^63)        -- 0
#eval neg_f (-2^63 + 1)    -- 0
#eval neg_f (-2^62 - 1)    -- 0

-- ...
#eval neg_f (-2^62)         -- 1


#eval neg_f (-5)            -- 60
-- [-4, -2)
#eval neg_f (-4)            -- 61
#eval neg_f (-3)            -- 61
-- [-2, -1)
#eval neg_f (-2)            -- 62
#eval neg_f (-1)            -- 62

-- [0, 1]
#eval zer_f 0               -- 63
#eval zer_f 1               -- 63

-- (1, 2]
#eval pos_f 2               -- 64

-- (3, 4]
#eval pos_f 3               -- 65
#eval pos_f 4               -- 65

-- ...
#eval pos_f (2^61 - 2)      -- 124
#eval pos_f (2^61 - 1)      -- 124
#eval pos_f (2^61)          -- 124

--(2^61, 2^62]
#eval pos_f (2^61 + 1)      -- 125
#eval pos_f (2^62 - 2)      -- 125
#eval pos_f (2^62 - 1)      -- 125
#eval pos_f (2^62)          -- 125

-- (2^62, 2^63]
#eval pos_f (2^62 + 1)      -- 126
#eval pos_f (2^63 - 1)      -- 126
#eval pos_f (2^63)          -- 126
-/



-- Number of bins
def logLongBins_bins : ℕ := 127

/--
Logarithmic binning definition for the Long type. See (CITEME).
-/
def logLongBins_def (l : Long) : ℕ :=
  if (l.val = 0 ∨ l.val = 1) then 63
  else if (l.val < 0) then 62 - Nat.log 2 (Int.toNat (-l.val - 1))
  else Nat.log 2 (Int.toNat l.val - 1) + 64

-- set_option pp.notation false

lemma logLongBins_wf : logLongBins_def t < logLongBins_bins := by
  simp [logLongBins_def, logLongBins_bins]
  split
  case inl =>
    -- Zero case
    omega
  split
  case inr.inl =>
    rename_i Hlz Hnz
    trans
    · apply Nat.sub_lt
      · omega
      · -- apply Nat.sub_lt_left_of_lt_add
        refine Nat.log_pos_iff.mpr ?a.a
        apply And.intro
        · apply Nat.le_sub_of_add_le
          simp
          -- Uh oh is this true?
          sorry
        · linarith
    · omega
    --
  case inr.inr =>
    rename_i Hnlz Hnz
    apply Nat.add_lt_of_lt_sub
    simp
    apply Nat.log_lt_of_lt_pow
    · simp
      sorry
    · rcases t with ⟨ A , B ⟩
      simp only [not_or, not_lt] at *
      rcases B with ⟨ B1 , B2 ⟩
      rcases Hnlz with ⟨ A1, A2 ⟩
      rw [LongMAX] at B2
      rw [Int.toNat]
      cases A
      · simp only []
        -- rw [Int.ofNat] at B2
        -- Uh oh is this true either?
        sorry
      · simp

/--
Logarithmic binning method for the Long type.
-/
def logLongBins : Bins Long logLongBins_bins :=
  Bins.mk (fun t => (Fin.mk (logLongBins_def t) logLongBins_wf))


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
  apply Nat.sub_one_lt_of_le Hv
  exact Nat.le_refl v


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
  let mechRec :=
    match n with
    | Nat.zero => (fun _ => PMF.pure (emptyHistogram numBins B))
    | Nat.succ n' => privNoisedHistogramAux ε₁ ε₂ n' (Nat.lt_of_succ_lt Hn)
  privPostProcess
    (privCompose (privNoisedBinCount numBins B ε₁ ε₂ n) mechRec)
    (fun z => match z with | (vₙ , h') => (setCount numBins B h' n vₙ))


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
