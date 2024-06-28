/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan, Markus de Medeiros
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Lean.Elab.Tactic


/-!
# Logarithm on ENNReal

In this file we extend the logarithm to ``ENNReal``.

The main definitions in this file are
- ``ofEReal : EReal -> ENNReal`` : Casting ``EReal`` to ``ENNReal`` by truncation
- ``eexp : EReal -> ENNReal`` : Exponential extended to the ``EReal``s
- ``elog : ENNReal -> EReal`` : Logarithm extended to the ``ENNReal``s
-/

noncomputable section

open scoped Classical
open ENNReal EReal Real



section EReal_conv_cases
/-!
### Case analysis lemmas

Most conversion proofs follow by splitting into cases, and then simplifying. However
explicitly performing case analysis can be unwieldy and lead to lots of duplicate work,
depending on which simplification rules are used. These tactics allow us to fine-tune the
case splits at the start of a conversion proof in order to reduce the number of cases we must
prove by hand.


Tactic overview:

Real numbers:
- ``case_Real_zero``: A real number is zero or nonzero
- ``case_Real_sign``: A real number is negative, zero, or positive
- ``case_nonneg_zero``: Given ``0 ≤ r``, `r` is zero or positive
- ``case_Real_nonnegative`` : A real number is negative or nonnegative

Extended nonnegative real numbers:
- ``case_ENNReal_isReal``: An ``ENNReal`` is ⊤, or the cast of a real number
- ``case_ENNReal_isReal_zero``: An ``ENNReal`` is ⊤, zero, or the cast of a real number

Extended reals:
- ``case_EReal_isReal``: An ``EReal`` is ⊤, ⊥, or the cast of a real number
- ``case_EReal_isENNReal``: An `EReal`` is negative, or the cast of an ``ENNReal``
-/


/--
A real number is either zero or nonzero
-/
lemma Real_cases_zero (r : ℝ) : r = 0 ∨ r ≠ 0 := by
  exact eq_or_ne r (OfNat.ofNat 0)

syntax "case_Real_zero" term : tactic
macro_rules
| `(tactic| case_Real_zero $r:term ) =>
    `(tactic| rcases (eq_or_ne $r (OfNat.ofNat 0)) with _ | _ <;> try simp_all)



/--
A real number is either negative, zero, or postive
-/
lemma Real_cases_sign (r : ℝ) : r < 0 ∨ r = 0 ∨ 0 < r := by exact lt_trichotomy r (OfNat.ofNat 0)

syntax "case_Real_sign" term : tactic
macro_rules
| `(tactic| case_Real_sign $r:term ) =>
    `(tactic| rcases (Real_cases_sign $r) with _ | _ | _ <;> try simp_all)

/--
A nonnegative number is either zero or positive
-/
syntax "case_nonneg_zero" term : tactic
macro_rules
| `(tactic| case_nonneg_zero $H:term ) =>
    `(tactic| rcases (LE.le.eq_or_gt $H) with _ | _ <;> try simp_all)



/--
A real number is either negative, or nonzero
-/
lemma Real_cases_nonnegative (r : ℝ) : r < 0 ∨ 0 ≤ r := by exact lt_or_le r (OfNat.ofNat 0)

syntax "case_Real_nonnegative " term : tactic
macro_rules
| `(tactic| case_Real_nonnegative $r:term ) =>
    `(tactic| rcases (Real_cases_nonnegative $r) with _  | _  <;> try simp_all)


lemma ENNReal_isReal_cases (x : ENNReal) : x = ⊤ ∨ (∃ v : ℝ, x = ENNReal.ofReal v ∧ 0 ≤ v) := by
  cases x
  · left
    simp
  . right
    rename_i v
    rcases v with ⟨ r, Hr ⟩
    exists r
    apply And.intro
    · simp [ENNReal.ofReal, Real.toNNReal]
      congr
      rw [max_eq_left Hr]
    · assumption

syntax "case_ENNReal_isReal" term : tactic
macro_rules
| `(tactic| case_ENNReal_isReal $w:term ) =>
    `(tactic| rcases (ENNReal_isReal_cases $w) with  _ | ⟨ _, _, _⟩ <;> try simp_all)

/--
An ENNReal is either top, zero, or the lift if a positive real
-/
lemma ENNReal_isReal_zero_cases (x : ENNReal) : x = ⊤ ∨ x = 0 ∨ (∃ v : ℝ, x = ENNReal.ofReal v ∧ 0 < v) := by
  case_ENNReal_isReal x
  rename_i r Hr1 Hr2
  case_nonneg_zero Hr2
  right
  exists r

syntax "case_ENNReal_isReal_zero" term : tactic
macro_rules
| `(tactic| case_ENNReal_isReal_zero $w:term ) =>
    `(tactic| rcases (ENNReal_isReal_zero_cases $w) with  _ | _ | ⟨ _, _, _⟩ <;> try simp_all)

/--
An EReal is either ⊤, ⊥, or the lift of some real number.
-/
lemma EReal_isReal_cases (w : EReal) : w = ⊥ ∨ w = ⊤ ∨ (∃ v : ℝ, w = Real.toEReal v) := by
  cases w
  · left
    rfl
  rename_i w'
  cases w'
  · right
    left
    rfl
  rename_i wR
  right
  right
  exists wR

syntax "case_EReal_isReal" term : tactic
macro_rules
| `(tactic| case_EReal_isReal $w:term ) =>
    `(tactic| rcases (EReal_isReal_cases $w) with _ | _ | ⟨ _, _ ⟩ <;> try simp_all)

/--
An EReal is either negative, or the lift of an ENNReal
-/
lemma EReal_isENNReal_cases (w : EReal) : (w < 0) ∨ (∃ v : ENNReal, w = ENNReal.toEReal v) := by
  case_EReal_isReal w
  · exists ⊤
  · rename_i w' Hw'
    case_Real_nonnegative w'
    rename_i Hw''
    right
    exists (ENNReal.ofReal w')
    simp only [coe_ennreal_ofReal, EReal.coe_eq_coe_iff]
    rw [max_eq_left Hw'']

syntax "case_EReal_isENNReal" term : tactic
macro_rules
| `(tactic| case_EReal_isENNReal $w:term ) =>
    `(tactic| rcases (EReal_isENNReal_cases $w) with _ | ⟨ _, _ ⟩ <;> try simp_all)


end EReal_conv_cases



namespace ENNReal

section ofEReal
/-!
### Coercion from EReals to ENNreals
-/


/--
Truncate an `EReal` to an `ENNReal`
-/
noncomputable def ofEReal (e : EReal) : ENNReal :=
  match e with
  | ⊥ => some 0
  | ⊤ => ⊤
  | some (some r) => ENNReal.ofReal r

@[simp]
lemma ofEReal_bot : ofEReal ⊥ = 0 := by simp [ofEReal]

@[simp]
lemma ofEReal_top : ofEReal ⊤ = ⊤ := by simp [ofEReal]

@[simp]
lemma ofEReal_zero : ofEReal 0 = 0 := by simp [ofEReal]

@[simp]
lemma ofEReal_real (r : ℝ) : ofEReal r = ENNReal.ofReal r := by simp [Real.toEReal, ofEReal]


lemma ofEReal_eq_zero_iff (w : EReal) : w ≤ 0 <-> ofEReal w = 0 := by
  apply Iff.intro
  · intro _
    case_EReal_isReal w
  · intro _
    case_EReal_isReal w

/--
``ofEReal`` is injective for for positive EReals
-/
lemma ofEReal_nonneg_inj {w z : EReal} (Hw : 0 <= w) (Hz : 0 <= z) :
  w = z <-> (ofEReal w = ofEReal z) := by
  apply Iff.intro
  · intro _
    simp_all
  · intro Heq
    all_goals case_EReal_isReal w
    all_goals case_EReal_isReal z

@[simp]
lemma toEReal_ofENNReal_nonneg {w : EReal} (H : 0 ≤ w) : ENNReal.toEReal (ofEReal w) = w := by case_EReal_isReal w

@[simp]
lemma ofEReal_toENNReal {x : ENNReal} : ofEReal (ENNReal.toEReal x) = x := by case_ENNReal_isReal x

/-
`ENNReal.ofReal` is the composition of cases from Real to EReal to ENNReal
-/
@[simp]
lemma ofEReal_ofReal_toENNReal : ENNReal.ofEReal (Real.toEReal r) = ENNReal.ofReal r := by
  simp [ofEReal, Real.toEReal, ENNReal.ofReal]


lemma ofEReal_le_mono {w z : EReal} (H : w ≤ z) : ofEReal w ≤ ofEReal z := by
  all_goals case_EReal_isReal w
  all_goals case_EReal_isReal z
  apply ofReal_le_ofReal
  assumption

-- True, and provable, but unused
-- lemma ofEReal_le_mono_conv_nonneg {w z : EReal} (Hw : 0 ≤ w) (Hle : ofEReal w ≤ ofEReal z) : w ≤ z := by
--   all_goals case_EReal_isENNReal w
--   all_goals case_EReal_isENNReal z
--   · exfalso
--     rename_i Hw' _
--     -- 0 <= w < 0
--     sorry
--   · exfalso
--     rename_i r Hw' Hr
--     -- 0 <= w < 0
--     sorry
--   · exfalso
--     rename_i r Hr Hz'
--     -- 0 <= w <= z < 0
--     sorry



 @[simp]
 lemma ofEReal_plus_nonneg (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w + z) = ofEReal w + ofEReal z := by
   all_goals case_EReal_isReal w
   all_goals case_EReal_isReal z
   rename_i w' z' _ _
   rw [← EReal.coe_add]
   rw [ofEReal_ofReal_toENNReal]
   rw [ofReal_add Hw Hz]



@[simp]
lemma ofEReal_mul_nonneg (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w * z) = ofEReal w * ofEReal z := by
  all_goals case_EReal_isReal w
  all_goals case_EReal_isReal z
  · rename_i r _ _
    case_nonneg_zero Hz
    rename_i Hr_nz
    simp [top_mul_coe_of_pos Hr_nz]
  · rename_i r Hr Hz'
    case_nonneg_zero Hw
    rename_i Hr_nz
    simp [coe_mul_top_of_pos Hr_nz]
  · rw [← EReal.coe_mul]
    rw [ofEReal_ofReal_toENNReal]
    rw [ofReal_mul' Hz]



lemma ofEReal_nonneg_scal_l {r : ℝ} {w : EReal} (H1 : 0 < r) (H2 : 0 ≤ r * w) : 0 ≤ w := by
  all_goals case_EReal_isReal w
  · exfalso
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr H1)] at H2
    simp at H2
  · rename_i w' Hw'
    rw [← EReal.coe_mul] at H2
    apply EReal.coe_nonneg.mp at H2
    exact nonneg_of_mul_nonneg_right H2 H1

end ofEReal


/--
``ENNReal.ofReal`` is injective for for positive EReals
-/
lemma ofReal_injective_nonneg {r s : ℝ} (HR : 0 ≤ r) (HS : 0 ≤ s) (H : ENNReal.ofReal r = ENNReal.ofReal s) : r = s := by
  apply (Real.toNNReal_eq_toNNReal_iff HR HS).mp
  simp [ENNReal.ofReal] at H
  assumption




section elog_eexp

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

-- MARKUSDE: cleanup?
@[simp]
lemma elog_of_pos_real {r : ℝ} (H : 0 < r) : elog (ENNReal.ofReal r) = Real.log r := by
  rw [elog]
  split
  · simp at *
  · split
    · rename_i r' heq h
      exfalso
      rw [h] at heq
      simp at heq
      linarith
    · rename_i h' r' heq h
      simp_all
      congr
      simp [ENNReal.ofReal] at heq
      rw [<- heq]
      exact (Real.coe_toNNReal r (le_of_lt H))

@[simp]
lemma elog_zero : elog 0 = ⊥ := by simp [elog]

@[simp]
lemma elog_top : elog ⊤ = ⊤ := by simp [elog]

@[simp]
lemma eexp_bot : eexp ⊥ = 0 := by simp [eexp]

@[simp]
lemma eexp_top : eexp ⊤ = ⊤ := by simp [eexp]

@[simp]
lemma eexp_zero : eexp 0 = 1 := by simp [eexp]

@[simp]
lemma eexp_ofReal {r : ℝ} : eexp r = ENNReal.ofReal (Real.exp r) := by
  simp [ENNReal.ofReal, eexp, elog]
  rfl

@[simp]
lemma elog_eexp {x : ENNReal} : eexp (elog x) = x := by
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
lemma eexp_elog {w : EReal} : (elog (eexp w)) = w := by
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
      · rename_i Hcont
        have Hcont' : 0 < rexp v'' := by exact exp_pos v''
        linarith
      · rename_i H
        have RW : (max (rexp v'') 0) = (rexp v'') := by
          apply max_eq_left_iff.mpr
          linarith
        simp [RW]
        clear RW
        simp [Real.toEReal]


lemma elog_ENNReal_ofReal_of_pos {x : ℝ} (H : 0 < x) : (ENNReal.ofReal x).elog = x.log.toEReal := by
  simp [ENNReal.ofReal, ENNReal.elog, ENNReal.toEReal]
  rw [ite_eq_iff']
  apply And.intro
  · intro
    exfalso
    linarith
  · intro H
    simp at H
    rw [max_eq_left_of_lt H]

@[simp]
lemma elog_mul {x y : ENNReal} : elog x + elog y = elog (x * y) := by
  all_goals case_ENNReal_isReal_zero x
  all_goals case_ENNReal_isReal_zero y
  rename_i r₁ Hr₁ HPr₁ r₂ Hr₂ HPr₂
  rw [← EReal.coe_add]
  rw [<- Real.log_mul ?G1 ?G2]
  case G1 => linarith
  case G2 => linarith
  rw [<- elog_ENNReal_ofReal_of_pos ?G1]
  case G1 => exact Real.mul_pos HPr₁ HPr₂
  rw [ENNReal.ofReal_mul]
  linarith


@[simp]
lemma eexp_add {w z : EReal} : eexp w * eexp z = eexp (w + z) := by
  all_goals case_EReal_isReal w
  all_goals case_EReal_isReal z
  · apply top_mul
    simp
    apply exp_pos
  · apply mul_top
    simp
    apply exp_pos
  rw [← EReal.coe_add]
  rw [<- ENNReal.ofReal_mul ?G1]
  case G1 => apply exp_nonneg
  rw [← exp_add]
  rw [eexp_ofReal]


lemma eexp_injective {w z : EReal} : eexp w = eexp z -> w = z := by
  rw [eexp, eexp]
  intro H
  cases w <;> cases z <;> try tauto
  · rename_i v
    cases v <;> simp at *
    rename_i v'
    have Hv' := exp_pos v'
    linarith
  · rename_i v
    cases v <;> simp at *
    rename_i v'
    have Hv' := exp_pos v'
    linarith
  · rename_i v₁ v₂
    cases v₁ <;> cases v₂ <;> simp at *
    congr
    rename_i v₁' v₂'
    simp [ENNReal.ofReal] at H
    apply NNReal.coe_inj.mpr at H
    simp at H
    have RW (r : ℝ) : (max (rexp r) 0) = (rexp r) := by
      apply max_eq_left_iff.mpr
      exact exp_nonneg r
    rw [RW v₁'] at H
    rw [RW v₂'] at H
    exact exp_eq_exp.mp H


lemma elog_injective {x y : ENNReal} : elog x = elog y -> x = y := by
  all_goals case_ENNReal_isReal_zero x
  all_goals case_ENNReal_isReal_zero y
  rename_i r₁ Hr₁ HPr₁ r₂ Hr₂ HPr₂
  intro Hlog_eq
  suffices r₁ = r₂ by simp [this]
  apply Real.log_injOn_pos
  all_goals simp_all


lemma eexp_zero_iff {w : EReal} : eexp w = 0 <-> w = ⊥ := by
  apply Iff.intro
  · intro H
    all_goals case_EReal_isReal w
    rename_i r _
    have Hcont := exp_pos r
    linarith
  · simp_all


lemma elog_bot_iff {x : ENNReal} : elog x = ⊥ <-> x = 0 := by
  apply Iff.intro
  · intro H
    all_goals case_ENNReal_isReal_zero x
  · simp_all



lemma eexp_mono_lt {w z : EReal} : (w < z) <-> eexp w < eexp z := by
  apply Iff.intro
  · intro H
    all_goals case_EReal_isReal w
    · apply bot_lt_iff_ne_bot.mpr
      apply bot_lt_iff_ne_bot.mp at H
      intro HK
      apply H
      apply eexp_zero_iff.mp
      simp_all
    all_goals case_EReal_isReal z
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?G1).mpr
    case G1 => apply exp_nonneg
    exact exp_lt_exp.mpr H
  · intro H
    all_goals case_EReal_isReal w
    · apply bot_lt_iff_ne_bot.mpr
      intro HK
      have H'' : 0 ≠ eexp z := by exact ne_of_lt H
      apply H''
      symm
      apply eexp_zero_iff.mpr
      assumption
    all_goals case_EReal_isReal z
    rename_i a _ _ _
    have C1 : OfNat.ofNat 0 ≤ rexp a := by exact exp_nonneg a
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg C1).mp at H
    exact exp_lt_exp.mp H



lemma eexp_mono_le {w z : EReal} : (w <= z) <-> eexp w <= eexp z := by
  apply Iff.intro
  · intro H
    cases (LE.le.lt_or_eq H)
    · apply LT.lt.le
      apply eexp_mono_lt.mp
      assumption
    · simp_all
  · intro H
    cases (LE.le.lt_or_eq H)
    · apply LT.lt.le
      apply eexp_mono_lt.mpr
      assumption
    · apply Eq.le
      apply eexp_injective
      assumption



lemma elog_mono_lt {x y : ENNReal} : (x < y) <-> elog x < elog y := by
  apply Iff.intro
  · intro H
    all_goals case_ENNReal_isReal_zero x
    · apply Ne.bot_lt'
      intro HK
      symm at HK
      apply elog_bot_iff.mp at HK
      simp [HK] at H
    all_goals case_ENNReal_isReal_zero y
    apply log_lt_log
    · assumption
    · assumption
  · intro H
    all_goals case_ENNReal_isReal_zero x
    · apply Ne.bot_lt'
      intro HK
      symm at HK
      simp [HK] at H
    all_goals case_ENNReal_isReal_zero y
    apply (Real.log_lt_log_iff ?G1 ?G2).mp <;> assumption




lemma elog_mono_le {x y : ENNReal} : (x <= y) <-> elog x <= elog y := by
  apply Iff.intro
  · intro H
    cases (LE.le.lt_or_eq H)
    · apply LT.lt.le
      apply elog_mono_lt.mp
      assumption
    · simp_all
  · intro H
    cases (LE.le.lt_or_eq H)
    · apply LT.lt.le
      apply elog_mono_lt.mpr
      assumption
    · apply Eq.le
      apply elog_injective
      assumption


end elog_eexp





section misc


lemma mul_mul_inv_le_mul_cancel {x y : ENNReal} : (x * y⁻¹) * y ≤ x := by
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

lemma mul_mul_inv_eq_mul_cancel {x y : ENNReal} (H : y = 0 -> x = 0) (H2 : ¬(x ≠ 0 ∧ y = ⊤)) : (x * y⁻¹) * y = x := by
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

lemma ereal_smul_le_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w ≤ s * z) : w ≤ z := by
  have defTop : some none = (⊤ : EReal) := by simp [Top.top]
  have defBot : none = (⊥ : EReal) := by simp [Bot.bot]

  cases s
  · exfalso
    rw [defBot] at Hr1
    simp_all only [not_lt_bot]
  rename_i s_nnr
  cases s_nnr
  · rw [defTop] at Hr2
    exfalso
    simp_all only [EReal.zero_lt_top, lt_self_iff_false]
  rename_i s_R
  have Hsr : some (some s_R) = Real.toEReal s_R := by simp [Real.toEReal]
  rw [Hsr] at H
  rw [Hsr] at Hr1
  rw [Hsr] at Hr2
  clear Hsr

  cases w
  · apply left_eq_inf.mp
    rfl
  rename_i w_nnr
  cases w_nnr
  · simp [defTop] at H
    rw [EReal.mul_top_of_pos Hr1] at H
    have X1 : z = ⊤ := by
      cases z
      · exfalso
        simp at H
        rw [defBot] at H
        rw [EReal.mul_bot_of_pos] at H
        · cases H
        · apply Hr1
      rename_i z_nnr
      cases z_nnr
      · simp [Top.top]
      exfalso
      apply top_le_iff.mp at H
      rename_i z_R
      have Hzr : some (some z_R) = Real.toEReal z_R := by simp [Real.toEReal]
      rw [Hzr] at H
      rw [<- EReal.coe_mul] at H
      cases H
    rw [defTop, X1]
  rename_i w_R
  cases z
  · simp [defBot] at H
    rw [EReal.mul_bot_of_pos] at H
    apply le_bot_iff.mp at H
    · rw [defBot]
      have Hwr : some (some w_R) = Real.toEReal w_R := by simp [Real.toEReal]
      rw [Hwr] at H
      rw [<- EReal.coe_mul] at H
      cases H
    · apply Hr1
  rename_i z_nnr
  cases z_nnr
  · exact right_eq_inf.mp rfl
  rename_i z_R
  have Hwr : some (some w_R) = Real.toEReal w_R := by simp [Real.toEReal]
  have Hzr : some (some z_R) = Real.toEReal z_R := by simp [Real.toEReal]
  rw [Hwr, Hzr] at H
  rw [Hwr, Hzr]
  clear Hwr
  clear Hzr
  apply EReal.coe_le_coe_iff.mpr
  repeat rw [<- EReal.coe_mul] at H
  apply EReal.coe_le_coe_iff.mp at H
  apply le_of_mul_le_mul_left H
  exact EReal.coe_pos.mp Hr1

lemma ereal_smul_eq_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w = s * z) : w = z := by
  apply LE.le.antisymm
  · apply ereal_smul_le_left s Hr1 Hr2 (le_of_eq H)
  · apply ereal_smul_le_left s Hr1 Hr2 (le_of_eq (id (Eq.symm H)))

end misc

end ENNReal
