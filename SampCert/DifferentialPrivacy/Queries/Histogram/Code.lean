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


/--
A histogram with a fixed binning method and ``i+1`` bins

Counts in the histogram are permitted to be negative.
-/
structure Histogram (T : Type) (num_bins : ℕ+) (B : Bins T num_bins) where
  count : Vector ℤ num_bins

/-!
## Private Histograms
-/
noncomputable section

namespace SLang

variable (numBins : ℕ+)

def predBins : ℕ := numBins.natPred

def predBins_lt_numBins : predBins numBins < numBins := by
  rw [predBins]
  cases numBins
  rename_i v Hv
  simp
  apply Nat.sub_one_lt_of_le Hv
  exact Nat.le_refl v

variable {T : Type}
variable (B : Bins T numBins)
variable [dps : DPSystem T]

/--
Construct an empty histagram
-/
def emptyHistogram : Histogram T numBins B :=
  Histogram.mk (Vector.replicate numBins 0)

-- /-
-- Increment the count of one element in a histogram
-- -/
-- def tickHistogram  (h : Histogram T i.succ B) (t : T) : Histogram T i.succ B :=
--   let t_bin := B.bin t
--   let t_count := Vector.get h.count t_bin + 1
--   { h with count := Vector.set h.count t_bin t_count }


-- Prove that this is 1-sensitive

def exactBinCount (b : Fin numBins) (l : List T) : ℤ :=
  List.length (List.filter (fun v => B.bin v = b) l)


-- /-
-- Compute an exact histogram from a list of elements
-- -/
-- def exactHistogram (l : List T) : (Histogram T i.succ B) :=
--   -- List.foldl (tickHistogram i.succ B) (emptyHistogram i.succ B) l
--   -- This version is probably easier to extract from (and definitely easier to prove with)
--   { count := Vector.ofFn (fun b => exactBinCount i.succ B b l) }


-- Rewrite this to be easier to prove with, probably.
-- Want to use regular composition lemma

-- #check privCompose

-- def privNoisedHistogramAux (ε₁ ε₂ : ℕ+) (h : SLang (Histogram T i.succ B)) (n : Fin i.succ) : SLang (Histogram T i.succ B) :=
--   match n.val with
--   | Nat.zero => h
--   | Nat.succ n' => do
--     let hᵥ <- h
--     let (vₑ : ℤ) := hᵥ.count.get n
--
--     sorry

def privNoisedBinCount (ε₁ ε₂ : ℕ+) (b : Fin numBins) : Mechanism T ℤ :=
  (dps.noise (exactBinCount numBins B b) 1 ε₁ (ε₂ * numBins))

def setCount (h : Histogram T numBins B) (b : Fin numBins) (v : ℤ) : Histogram T numBins B :=
  { h with count := h.count.set b v }

-- def privNoisedHistogram (ε₁ ε₂ : ℕ+) (n : Fin i.succ) (l : List T) : SLang (Histogram T i.succ B) :=
--   (Nat.recOn (motive := fun (x : ℕ) => (x < i.succ) -> SLang (Histogram T i.succ B))
--     n.val
--     (fun _ => probPure (emptyHistogram i.succ B))
--     (fun n' IH Hn' => do
--       let (Hn'' : n' < i.succ) := Nat.lt_of_succ_lt Hn'
--       let (vₙ , h') <- privCompose (privNoisedBinCount i.succ B ε₁ ε₂ n) (fun _ => IH Hn'') l
--       probPure (setCount i.succ B h' n vₙ)))
--   n.isLt

-- Invariant: Result  is ``n.succ * (ε₁ / (ε₂ * numBins)``-DP
def privNoisedHistogramAux (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) (l : List T) : SLang (Histogram T numBins B) := do
  let (mechRec : Mechanism T (Histogram T numBins B)) :=
    match n with
    | Nat.zero => (fun _ => probPure (emptyHistogram numBins B))
    | Nat.succ n' => sorry
  let (vₙ , h') <- privCompose (privNoisedBinCount numBins B ε₁ ε₂ n) mechRec l
  probPure (setCount numBins B h' n vₙ)

/-
Histogram with noise added to each count
-/
def privNoisedHistogram (ε₁ ε₂ : ℕ+) : Mechanism T (Histogram T numBins B) :=
  privNoisedHistogramAux numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins)


-- def privNoisedHistogram (ε₁ ε₂ : ℕ+) (l : List T) : SLang (Histogram T i.succ B) := do
--   let count <- Vector.mOfFn (fun (b : Fin i.succ) => dps.noise (exactBinCount i.succ B b) 1 ε₁ ε₂ l)
--   return { count }


/-
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

def privMaxBinAboveThreshold (ε₁ ε₂ : ℕ+) (τ : ℤ) : Mechanism T (Option (Fin numBins)) :=
  privPostProcess
    (privNoisedHistogram numBins B ε₁ ε₂)
    (exactMaxBinAboveThresholdAux numBins B τ (predBins numBins) (predBins_lt_numBins numBins))


end SLang
