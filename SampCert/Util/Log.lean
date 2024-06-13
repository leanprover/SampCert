/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan, Markus de Medeiros
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Logarithm on ENNReal

In this file we extend the logarithm to ``ENNReal``.
-/

noncomputable section

open scoped Classical
open ENNReal EReal Real

namespace ENNReal

/--
The extended logarithm
-/
def elog (x : ENNReal) : EReal :=
  match x with
  | none => ⊤
  | some r => if r = 0 then ⊥ else Real.log r

/--
The extended exponential

Mathlib's has an extended ``rpow`` function of type ``ℝ≥0∞ → ℝ → ℝ≥0∞``, however we
want the exponent to be of type ``EReal``.
-/
def eexp (y : EReal) : ENNReal :=
  match y with
  | none => 0
  | (some none) => ⊤
  | (some (some r)) => ENNReal.ofReal (Real.exp r)

variable {x y : ENNReal}
variable {w z : EReal}
variable {r : Real}

@[simp]
lemma elog_of_pos_real (H : 0 < r) : elog (ENNReal.ofReal r) = Real.log r := by
  rw [elog]
  split
  · sorry
  · split
    · rename_i r heq h
      simp
      sorry
    · sorry

@[simp]
lemma elog_zero : elog (ENNReal.ofReal 0) = ⊥ := by sorry

@[simp]
lemma elog_top : elog ⊤ = ⊤ := by sorry

@[simp]
lemma eexp_bot : eexp ⊥ = 0 := by sorry

@[simp]
lemma eexp_top : eexp ⊤ = ⊤ := by sorry

@[simp]
lemma eexp_pos_real (H : 0 < r) : eexp r = ENNReal.ofReal (Real.log r) := by sorry

@[simp]
lemma elog_eexp : eexp (elog x) = x := by
  rw [elog]
  split
  · simp
  · rename_i _ r'
    split
    · simp
      rename_i _ h
      rw [h]
    · rename_i _ H
      simp
      rw [eexp]
      rw [NNReal.toReal, Real.toEReal]
      simp
      rw [Real.exp_log]
      rw [ofReal_coe_nnreal]
      rcases r' with ⟨ v , Hv ⟩
      apply lt_of_le_of_ne
      · simpa
      · simp
        intro Hk
        apply H
        apply NNReal.coe_eq_zero.mp
        simp
        rw [Hk]

@[simp]
lemma eexp_elog : (elog (eexp w)) = w := by
  sorry

@[simp]
lemma elog_mul : elog x * elog y = elog (x + y) := by sorry -- checked truth table

@[simp]
lemma eexp_add : eexp w * eexp z = eexp (w + z) := by sorry -- checked truth table

-- Log of power, log and exp inverses

lemma eexp_injective : eexp w = eexp z -> w = z := by
  rw [eexp, eexp]
  intro H
  cases w <;> cases z <;> try tauto
  · rename_i v
    cases v <;> simp at *
    sorry
  · rename_i v
    cases v <;> simp at *
    sorry
  · rename_i v₁ v₂
    cases v₁ <;> cases v₂ <;> simp at *
    congr
    sorry

lemma elog_injective : elog x = elog y -> x = y := by
  rw [elog, elog]
  cases x <;> cases y <;> try tauto
  · rename_i v
    cases v; simp at *
    sorry
  · rename_i v
    cases v; simp at *
    sorry
  · rename_i v₁ v₂
    cases v₁; cases v₂; simp at *
    sorry

lemma eexp_mono_lt : (w < z) <-> eexp w < eexp z := by

  sorry

lemma eexp_mono_le : (w <= z) <-> eexp w <= eexp z := by sorry

lemma elog_mono_lt : (x < y) <-> elog x < elog y := by sorry

lemma elog_mono_le : (x <= y) <-> elog x <= elog y := by sorry

-- iff for log positive

-- Special values

end ENNReal
