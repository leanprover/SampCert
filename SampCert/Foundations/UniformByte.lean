/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Util.Util
import SampCert.Foundations.Auto
import SampCert.Foundations.UniformP2

/-!
# ``probUniformByte`` Properties

This file contains lemmas about ``probUniformByte``, a ``SLang`` sampler for the
uniform distribution on bytes.

It also contains the derivation that ``probUniformP2`` is a uniform distribution.
-/


open Classical Nat PMF

namespace SLang


local instance : Finite UInt8 := by
  constructor
  · apply Equiv.ofBijective (fun v => v.val)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => {val := v : UInt8})
    simp [Function.RightInverse, Function.LeftInverse]



/--
ProbUniformByte is a proper distribution
-/
def probUniformByte_normalizes : HasSum probUniformByte 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold SLang.probUniformByte
  rw [division_def]
  rw [ENNReal.tsum_mul_right]
  simp only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_one_iff _).mp
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.tsum_toReal_eq ?G1]
  case G1 => simp
  simp only [ENNReal.one_toReal]
  simp only [tsum_const]
  simp only [nsmul_eq_mul, mul_one]
  rw [@Nat.card_eq_of_equiv_fin UInt8 256 ?G1]
  case G1 =>
    apply Equiv.ofBijective (fun v => v.val)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => {val := v : UInt8})
    simp [Function.RightInverse, Function.LeftInverse]
  simp [ENNReal.toReal_inv]

/--
ProbUniformByte as a PMF
-/
def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

-- Might not be used

-- /-
-- Evaluation of ``probUniformByteUpperBits`` for zero-shifts inside the support
-- -/
-- def probUniformByteUpperBits_eval_overshift_support {i x : ℕ} (Hi : 8 ≤ i) (Hx : x < UInt8.size) :
--     probUniformByteUpperBits i x = 1 / UInt8.size := sorry
--
-- /-
-- Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-- -/
-- def probUniformByteUpperBits_eval_overshift_nil {i x : ℕ} (Hi : 8 ≤ i) (Hx : x ≥ UInt8.size) :
--     probUniformByteUpperBits i x = 0 := sorry

/--
Evaluation of ``probUniformByteUpperBits`` for inside the support
-/
def probUniformByteUpperBits_eval_support {i x : ℕ} (Hx : x < 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 2^(8 - i) / UInt8.size := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]
  cases (Classical.em (i < 8))

  · -- Simplify body
    rw [max_eq_left (by linarith)]
    rw [min_eq_right (by linarith)] at Hx
    conv =>
      enter [1, 1, a]
      rw [Nat.shiftRight_eq_div_pow]
    conv =>
      enter [1, 1, a]
      rw [<- mul_one (256)⁻¹]
      rw [<- mul_zero (256)⁻¹]
      rw [<- mul_ite]
    rw [ENNReal.tsum_mul_left]
    rw [division_def]
    rw [mul_comm]
    congr 1

    -- Restruct sum to type where body is constant
    rw [<- (@tsum_subtype_eq_of_support_subset  _ _ _ _ _ { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } ?G1)]
    case G1 => simp [Function.support]
    generalize HT : { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } = T
    have H (x1 : T) : (@ite _ (x = (x1 : UInt8).toNat / 2 ^ (8 - i)) _ (1 : ENNReal) (0 : ENNReal)) = 1 := by
      apply ite_eq_iff.mpr
      simp
      rcases x1
      rename_i h val property
      subst HT
      simp_all only
      simp_all only [Set.mem_setOf_eq]
    conv =>
      enter [1, 1, a]
      rw [H a]
    clear H

    -- Rewrite to real sum
    -- Simplify me
    suffices ENNReal.toReal (∑' (a : T), 1) = ENNReal.toReal (2 ^ (8 - i)) by
      refine (ENNReal.toReal_eq_toReal_iff' ?G1 ?G2).mp this
      case G1 =>
        rw [tsum_eq_finsum ?G1]
        case G1 =>
          simp [Function.support]
          apply Set.finite_univ_iff.mpr
          apply Subtype.finite
        simp
        have R := @finsum_induction ENNReal T _ (fun _ => 1) (fun z => z ≠ ⊤) (by simp) (by aesop) (by simp)
        simp at R
        trivial
      case G2 => simp

    -- Rewrite to set cardinality
    rw [ENNReal.tsum_toReal_eq ?G1]
    case G1 => simp
    simp [tsum_const]

    -- Evaluate set cardinality using bijection
    rw [@Nat.card_eq_of_equiv_fin T (2^(8 - i)) ?G1]
    case G1 =>
      rw [<- HT]
      simp
      -- Apply Euclidean division in order to construct the functions
      let f (t : { i_1 // x = (i_1 : UInt8).toNat / 2 ^ (8 - i) }) : Fin (2^(8-i)) :=
        let ⟨ t', HT' ⟩ := t
        sorry
      let g (t : Fin (2^(8-i))) : { i_1 // x = (i_1 : UInt8).toNat / 2 ^ (8 - i) } := sorry
      apply Equiv.ofBijective f
      apply Function.bijective_iff_has_inverse.mpr
      exists g
      dsimp [Function.RightInverse, Function.LeftInverse, f, g]
      sorry
    simp
  · rw [max_eq_right (by linarith)]
    rw [min_eq_left (by linarith)] at Hx
    rw [tsum_eq_single (UInt8.ofNatCore x Hx) ?G1]
    case G1 =>
      intro b' Hb'
      simp
      intro Hx'
      exfalso
      apply Hb'
      rcases b' with ⟨ ⟨ b'', Hb'' ⟩ ⟩
      simp [UInt8.ofNatCore]
      congr
      rw [Hx']
      simp [UInt8.toNat]
    simp
    intro HK
    exfalso
    apply HK
    rfl


/--
Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-/
def probUniformByteUpperBits_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 0 := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]
  intro v H1
  exfalso
  cases (Classical.em (i < 8))
  · -- i < 8
    rename_i Hi
    rw [max_eq_left (by linarith)] at H1
    rw [min_eq_right (by linarith)] at Hx
    simp_all
    rw [Nat.shiftRight_eq_div_pow] at *
    have H2 := UInt8.toNat_lt v
    apply Nat.mul_le_of_le_div (2 ^ (8 - i)) (2 ^ i) v.toNat at Hx
    rw [<- pow_add] at Hx
    have X : (i + (8 - i)) = 8 := by
      apply add_sub_of_le
      linarith
    rw [X] at Hx
    clear X
    linarith
  · -- i >= 8
    rename_i Hi
    rw [max_eq_right (by linarith)] at H1
    rw [min_eq_left (by linarith)] at Hx
    have H2 := UInt8.toNat_lt v
    simp_all
    linarith


lemma UIint8_cast_lt_size (a : UInt8) : a.toNat < UInt8.size := by
  rcases a with ⟨ ⟨ a', Ha' ⟩ ⟩
  rw [UInt8.toNat]
  simp
  apply Ha'


/--
Evaluation of ``probUniformP2`` for inside the support
-/
def probUniformP2_eval_support {i x : ℕ} (Hx : x < 2 ^ i):
    probUniformP2 i x = (1 / 2 ^ i) := by
  revert x
  induction' i using Nat.strong_induction_on with i ih
  rw [probUniformP2]
  split
  · intro x Hx'
    rename_i h
    rw [probUniformByteUpperBits_eval_support]
    · rw [UInt8.size]
      have X : 256 = 2^8 := by simp
      rw [X]
      clear X
      rw [cast_pow]
      apply (ENNReal.div_eq_div_iff _ _ _ _).mpr <;> try simp
      rw [← pow_add]
      congr 1
      rw [add_tsub_cancel_iff_le]
      linarith
    · rw [min_eq_right ?G1]
      case G1 => linarith
      assumption
  · intro x Hx'
    simp [probUniformByte]

    -- Simplify, rewrite to indicator function
    conv =>
      enter [1, 1, a]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, b]
      rw [<- mul_one (probUniformP2 (i - 8) b)]
      rw [<- mul_zero (probUniformP2 (i - 8) b)]
      rw [<- mul_ite]
      rw [<- mul_assoc]

    -- Similar to the Laplace proof: use Euclidean division to rewrite
    -- to product of indicator functions
    rcases @euclidean_division x UInt8.size (by simp) with ⟨ p, q, Hq, Hx ⟩
    have X (a : UInt8) (b : ℕ) D :
        (@ite _ (q + UInt8.size * p = UInt8.size * b + a.toNat) D (1 : ENNReal) 0) =
        (if p = b then (1 : ENNReal) else 0) * (if q = a.toNat then (1 : ENNReal) else 0) := by
      split
      · rename_i He
        conv at He =>
          enter [2]
          rw [add_comm]
        have R := (euclidean_division_uniquness _ _ _ _ (by simp) Hq ?G3).mp He
        case G3 => apply UIint8_cast_lt_size
        rcases R with ⟨ R1 , R2 ⟩
        simp_all
      · rename_i He
        suffices (p ≠ b) ∨ (q ≠ a.toNat) by
          rcases this with Ht | Ht
          · rw [ite_eq_right_iff.mpr]
            · simp
            · intro Hk
              exfalso
              apply Ht Hk
          · rw [mul_comm]
            rw [ite_eq_right_iff.mpr]
            · simp
            · intro Hk
              exfalso
              apply Ht Hk
        simp
        apply (Decidable.not_and_iff_or_not (p = b) (q = a.toNat)).mp
        intro HK
        apply He
        rw [And.comm] at HK
        have R := (euclidean_division_uniquness _ _ _ _ (by simp) Hq ?G3).mpr HK
        case G3 => apply UIint8_cast_lt_size
        linarith
    conv =>
      enter [1, 1, a, 1, b]
      rw [Hx]
      rw [X a b]
    clear X

    -- Separate the sums
    conv =>
      enter [1, 1, a, 1, b]
      repeat rw [mul_assoc]
    conv =>
      enter [1, 1, a]
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_left]
    conv =>
      enter [1, 2, 1, a, 1, b]
      rw [<- mul_assoc]
      rw [mul_comm]
    conv =>
      enter [1, 2, 1, a]
      rw [ENNReal.tsum_mul_left]
    conv =>
      enter [1, 2]
      rw [ENNReal.tsum_mul_right]
    simp

    -- Simplify the singleton sums
    rw [tsum_eq_single p ?G1]
    case G1 =>
      intro _ HK
      simp
      intro HK'
      exfalso
      exact HK (id (Eq.symm HK'))
    have X : (UInt8.ofNatCore q Hq).toNat = q := by
      rw [UInt8.ofNatCore, UInt8.toNat]
    rw [tsum_eq_single (UInt8.ofNatCore q Hq) ?G1]
    case G1 =>
      simp
      intro b HK' HK''
      apply HK'
      rw [UInt8.ofNatCore]
      rcases b with ⟨ ⟨ b' , Hb' ⟩ ⟩
      congr
      rw [HK'']
      rw [UInt8.toNat]
    rw [X]
    clear X
    simp

    -- Apply the IH
    rw [ih]
    · simp
      rw [<- ENNReal.mul_inv ?G1 ?G2]
      case G1 => simp
      case G2 => simp
      congr 1
      have H256 : (256 : ENNReal) = (256 : ℕ) := by simp
      rw [H256]
      have X : (256 : ℕ) = 2^8 := by simp
      rw [X]
      rw [cast_pow]
      rw [cast_two]
      rw [← pow_add]
      congr 1
      apply add_sub_of_le
      linarith
    · simp
      linarith
    · rw [Hx] at Hx'
      have Hx'' : UInt8.size * p < OfNat.ofNat 2 ^ i := by
        apply Classical.byContradiction
        intro HK
        linarith
      rw [UInt8.size] at Hx''
      have Y : 256 = 2^8 := by simp
      rw [Y] at Hx''
      clear Y
      have W := (Nat.lt_div_iff_mul_lt ?G1 _).mpr Hx''
      case G1 =>
        apply Nat.pow_dvd_pow (OfNat.ofNat 2)
        linarith
      apply (LT.lt.trans_eq W)
      apply Nat.pow_div <;> linarith

/--
Evaluation of ``probUniformP2`` for zero-shifts outside of the support
-/
def probUniformP2_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ i):
    probUniformP2 i x = 0 := by
  revert x
  induction' i using Nat.strong_induction_on with i ih
  intro x Hk
  rw [probUniformP2]
  split
  · apply probUniformByteUpperBits_eval_zero
    rw [min_eq_right]
    · trivial
    · linarith
  · simp
    intro i1
    right
    intro i2 Hi
    apply ih
    · sorry
    · rw [Hi] at Hk
      apply Classical.byContradiction
      intro Hk'
      simp_all
      -- ??

      sorry


/--
Evaluates the ``probUniformP2`` distribution at a point inside of its support.
-/
@[simp]
theorem UniformPowerOfTwoSample'_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
    UniformPowerOfTwoSample' n x = 1 / (2 ^ (log 2 n)) := by
  rw [UniformPowerOfTwoSample']
  rw [probUniformP2_eval_support h]

/--
Evaluates the ``probUniformP2`` distribution at a point outside of its support
-/
@[simp]
theorem UniformPowerOfTwoSample'_apply' (n : PNat) (x : Nat) (h : x ≥ 2 ^ (log 2 n)) :
    UniformPowerOfTwoSample' n x = 0 := by
  rw [UniformPowerOfTwoSample']
  apply probUniformP2_eval_zero
  linarith

/--
Equivalence between uniform samplers
-/
def probUniform_probUniform'_equiv (n : ℕ+) : UniformPowerOfTwoSample n = UniformPowerOfTwoSample' n := by
  apply SLang.ext
  intro x
  cases (Classical.em (x < 2 ^ (log 2 n)))
  · rename_i h
    rw [UniformPowerOfTwoSample_apply n x h]
    rw [← UniformPowerOfTwoSample'_apply n x h]
  · rename_i h'
    have h : x ≥ 2 ^ (log 2 n) := by linarith
    rw [UniformPowerOfTwoSample_apply' n x h]
    rw [← UniformPowerOfTwoSample'_apply' n x h]

end SLang
