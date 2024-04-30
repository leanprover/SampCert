/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.DP
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order

open Classical Nat Int Real

noncomputable section

namespace SLang

-- N+ and not Z because of sensitivity measure
-- Can be generalized
-- variable {T : Type} [Add T] [LinearOrder T] [coe: Coe T ℤ]
-- variable {h : Monotone coe.coe}

-- instance : OrderHom T ℤ where
--   toFun := coe.coe
--   monotone' := h

-- def BoundedSumQuery (clip₁ clip₂ : ℤ) (l : List ℤ) : ℤ :=
--   List.sum (List.map (fun n : ℤ => if n < clip₁ then clip₁ else if clip₂ < n then clip₂ else n) l)

def BoundedSumQuery (L U : ℤ) (l : List ℤ) : ℤ :=
  List.sum (List.map (fun n : ℤ => max (min n U) L) l)

-- theorem natAbs1 {n : ℕ} {x : ℤ} (h : n ≤ x) :
--   n ≤ natAbs x := by
--   cases x
--   . rename_i m
--     simp
--     exact Int.ofNat_le.mp h
--   . rename_i m
--     simp
--     have A : -[m+1] < 0 := negSucc_lt_zero m
--     have B : n < (0 : ℤ) := by
--       apply Int.lt_of_le_of_lt h A
--     contradiction

-- theorem natAbs2 {n : ℕ} {x : ℤ} (h : x ≤ -[n+1]) :
--   Nat.succ n ≤ natAbs x := by
--   cases x
--   . rename_i m
--     simp
--     have A : -[m+1] < 0 := negSucc_lt_zero m
--     have B : n < (0 : ℤ) := by
--       apply Int.lt_of_le_of_lt h A
--     contradiction
--   . rename_i m
--     simp
--     exact Int.ofNat_le.mp h

def maxBoundPos (L U : ℤ) (h : L < U) :
  0 < max (Int.natAbs L) (Int.natAbs U) := by
  have A : ¬ (L = 0 ∧ U = 0) := by
    by_contra h'
    cases h'
    rename_i h1 h2
    subst h1 h2
    contradiction
  simp at A
  have B : L = 0 ∨ L ≠ 0 := by exact eq_or_ne L 0
  cases B
  . rename_i h'
    subst h'
    simp at A
    simp
    trivial
  . rename_i h'
    simp
    left
    trivial

def maxBound (L U : ℤ) (h : L < U) : ℕ+ :=
  ⟨ max (Int.natAbs L) (Int.natAbs U) , maxBoundPos L U h⟩

theorem BoundedSumQuerySensitivity (L U : ℤ) (h : L < U) : sensitivity (BoundedSumQuery L U) (maxBound L U h) := by
  sorry
  -- simp [sensitivity, BoundedSumQuery]
  -- intros l₁ l₂ H
  -- cases H
  -- . rename_i a b n h1 h2
  --   subst h1 h2
  --   simp
  --   right
  -- . sorry
  -- . sorry

def NoisedBoundedSumQuery (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) (l : List ℤ) : SLang ℤ := do
  NoisedQuery (BoundedSumQuery L U) (maxBound L U h) ε₁ ε₂ l

theorem NoisedBoundedSumQueryDP (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedSumQuery L U h ε₁ ε₂) ε₁ ε₂ := by
  apply NoisedQueryDP
  apply BoundedSumQuerySensitivity

-- theorem BoundedSumSensitivity (clip₁ clip₂ : ℤ) (h : clip₁ < clip₂) : sensitivity (BoundedSumQuery clip₁ clip₂) (max (Int.natAbs clip₁) (Int.natAbs clip₂)) := by
--   simp [sensitivity, BoundedSumQuery]
--   intros l₁ l₂ H
--   cases H
--   . rename_i a b n h1 h2
--     subst h1 h2
--     simp
--     split
--     . left
--       apply le_refl
--     . split
--       . right
--         apply le_refl
--       . rename_i h3 h4
--         simp at *
--         cases n
--         . rename_i n
--           simp
--           right
--           simp at h4
--           apply natAbs1 h4
--         . rename_i n
--           simp at *
--           left
--           apply natAbs2 h3
--   . rename_i a n b h1 h2
--     subst h1 h2
--     simp
--     split
--     . left
--       apply le_refl
--     . split
--       . right
--         apply le_refl
--       . rename_i h3 h4
--         simp at *
--         cases n
--         . rename_i n
--           simp
--           right
--           simp at h4
--           apply natAbs1 h4
--         . rename_i n
--           simp at *
--           left
--           apply natAbs2 h3
--   . rename_i a n b m h1 h2
--     subst h1 h2
--     simp
--     split
--     . split
--       . rename_i h1 h2
--         simp at *
--       . split
--         . rename_i h1 h2 h3
--           simp at *
--           sorry
--         . rename_i h1 h2 h3
--           simp at *
--           sorry
--     . split
--       . split
--         . rename_i h1 h2 h3
--           simp at *

--           cases clip₁
--           . cases clip₂
--             . rename_i n' m'
--               simp at *
--               sorry
--             . rename_i n' m'
--               simp at *
--               sorry
--           . cases clip₂
--             . rename_i n' m'
--               simp at *
--               sorry
--             . rename_i n' m'
--               simp at *
--               sorry


--         . split
--           . rename_i h1 h2 h3 h4
--             simp at *
--           . rename_i h1 h2 h3 h4
--             simp at *
--             sorry
--       . split
--         . rename_i h1 h2 h3
--           simp at *
--           sorry
--         . split
--           . rename_i h1 h2 h3 h4
--             simp at *
--             sorry
--           . rename_i h1 h2 h3 h4
--             simp at *
--             sorry

end SLang
