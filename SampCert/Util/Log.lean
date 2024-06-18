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
Coerce a EReal to an ENNReal by truncation
-/
noncomputable def ofEReal (e : EReal) : ENNReal :=
  match e with
  | ⊥ => some 0
  | ⊤ => ⊤
  | some (some r) => ENNReal.ofReal r

-- instance : Coe EReal ENNReal := ⟨ofEReal⟩

/--
The extended logarithm
-/
def elog (x : ENNReal) : EReal :=
  match x with
  | ⊤ => ⊤
  | some r => if r = 0 then ⊥ else Real.log r

/--
The extended exponential

Mathlib's has an extended ``rpow`` function of type ``ℝ≥0∞ → ℝ → ℝ≥0∞``, however we
want the exponent to be of type ``EReal``.
-/
def eexp (y : EReal) : ENNReal :=
  match y with
  | ⊥ => 0
  | ⊤ => ⊤
  | some (some r) => ENNReal.ofReal (Real.exp r)


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
lemma elog_zero : elog (ENNReal.ofReal 0) = ⊥ := by simp [elog]

@[simp]
lemma elog_top : elog ⊤ = ⊤ := by simp [elog]

@[simp]
lemma eexp_bot : eexp ⊥ = 0 := by simp [eexp]

@[simp]
lemma eexp_top : eexp ⊤ = ⊤ := by simp [eexp]

@[simp]
lemma eexp_zero : eexp 0 = 1 := by simp [eexp]


@[simp]
lemma eexp_ofReal : eexp r = ENNReal.ofReal (Real.exp r) := by
  simp [ENNReal.ofReal, eexp, elog]
  rfl

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
      rw [NNReal.toReal]
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
  cases w
  · simp [eexp, elog]
    rfl
  · simp [eexp, elog]
    rename_i v'
    cases v'
    · simp
      rfl
    · simp
      rename_i v''
      simp [ENNReal.ofReal]
      split
      · -- exp is nonnegative
        sorry
      · sorry


@[simp]
lemma elog_mul : elog x * elog y = elog (x + y) := by

  sorry -- checked truth table

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

-- Need to write compat lemmas for ofEReal
-- Not sure which ones we'll need but


-- Specialized lemmas for ofEReal when its argument is nonnegative (so no truncation happens)
lemma ofEReal_nonneg_eq_iff (Hw : 0 <= w) (Hz : 0 <= z) : w = z <-> (ofEReal w = ofEReal z) :=
  sorry

lemma ofEReal_le_mono : (0 ≤ w) -> w ≤ z <-> (ofEReal w ≤ ofEReal z) :=
  sorry


@[simp]
lemma ofEReal_mul (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w * z) = ofEReal w * ofEReal z := sorry

@[simp]
lemma toEReal_ofENNReal_nonneg (H : 0 ≤ w) : ENNReal.toEReal (ofEReal w) = w := sorry


@[simp]
lemma ofEReal_toENNReal : ofEReal (ENNReal.toEReal x) = x := by sorry


-- ENNReal inequalities
-- These are needed to prove the extensded version of Jensen's inequality
lemma mul_mul_inv_le_mul_cancel : (x * y⁻¹) * y ≤ x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  simp
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

lemma mul_mul_inv_eq_mul_cancel (H : y = 0 -> x = 0) (H2 : ¬(x ≠ 0 ∧ y = ⊤)) : (x * y⁻¹) * y = x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  simp
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

end ENNReal
