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
Function to categorize values of type T into ``num_bins`` distinct bins.
-/
structure Bins (T : Type) (num_bins : ℕ) where
  bin : T -> Fin num_bins

-- This function is extracted already
#check Nat.log 2
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
        sorry
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
        sorry
      · simp

/--
Logarithmic binning method for the Long type.
-/
def logLongBins : Bins Long logLongBins_bins :=
  Bins.mk (fun t => (Fin.mk (logLongBins_def t) logLongBins_wf))


/--
A histogram with a fixed binning method.

Counts in the histogram are permitted to be negative.
-/
structure Histogram (T : Type) (num_bins : ℕ) (B : Bins T num_bins) where
  count : Vector ℤ num_bins

/-!
## Private Histograms
-/
noncomputable section

namespace SLang

variable {T : Type}
variable (num_bins : ℕ)
variable (B : Bins T num_bins)
variable [dps : DPSystem T]

/--
Construct an empty histagram
-/
def emptyHistogram : Histogram T num_bins B :=
  Histogram.mk (Vector.replicate num_bins 0)

-- /-
-- Increment the count of one element in a histogram
-- -/
-- def tickHistogram  (h : Histogram T num_bins B) (t : T) : Histogram T num_bins B :=
--   let t_bin := B.bin t
--   let t_count := Vector.get h.count t_bin + 1
--   { h with count := Vector.set h.count t_bin t_count }


-- Prove that this is 1-sensitive

def exactBinCount (b : Fin num_bins) (l : List T) : ℤ :=
  List.length (List.filter (fun v => B.bin v = b) l)


-- /-
-- Compute an exact histogram from a list of elements
-- -/
-- def exactHistogram (l : List T) : (Histogram T num_bins B) :=
--   -- List.foldl (tickHistogram num_bins B) (emptyHistogram num_bins B) l
--   -- This version is probably easier to extract from (and definitely easier to prove with)
--   { count := Vector.ofFn (exactBinCount num_bins B l) }


-- Rewrite this to be easier to prove with, probably.
-- Want to use regular composition lemma

/--
Histogram with noise added to each count
-/
def privNoisedHistogram (ε₁ ε₂ : ℕ+) (l : List T) : SLang (Histogram T num_bins B) := do
  let count <- Vector.mOfFn (fun (b : Fin num_bins) => dps.noise (exactBinCount num_bins B b) 1 ε₁ ε₂ l)
  return { count }



end SLang
