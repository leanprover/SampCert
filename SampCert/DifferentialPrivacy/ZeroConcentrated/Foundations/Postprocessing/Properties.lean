/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Postprocessing.Code

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable {T : Type}
variable [t1 : MeasurableSpace T]
variable [t2 : MeasurableSingletonClass T]

variable {U V : Type}
variable [m2 : MeasurableSpace U]
variable [count : Countable U]
variable [disc : DiscreteMeasurableSpace U]
variable [Inhabited U]

theorem condition_to_subset (f : U → V) (g : U → ENNReal) (x : V) :
  (∑' a : U, if x = f a then g a else 0) = ∑' a : { a | x = f a }, g a := by
  have A := @tsum_split_ite U (fun a : U => x = f a) g (fun _ => 0)
  simp only [decide_eq_true_eq, tsum_zero, add_zero] at A
  rw [A]
  have B : ↑{i | decide (x = f i) = true} = ↑{a | x = f a} := by
    simp
  rw [B]

theorem Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal) (mem : Memℒp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤)  :
  MeasureTheory.Integrable (fun x : T => (f x) ^ α.toReal) μ := by
  have X := @MeasureTheory.Memℒp.integrable_norm_rpow T ℝ t1 μ _ f α mem h1 h2
  revert X
  conv =>
    left
    left
    intro x
    rw [← norm_rpow_of_nonneg (nn x)]
  intro X
  simp [Integrable] at *
  constructor
  . cases X
    rename_i left right
    rw [@aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.pow_const
    simp [Memℒp] at mem
    cases mem
    rename_i left' right'
    rw [aestronglyMeasurable_iff_aemeasurable] at left'
    simp [left']
  . rw [← hasFiniteIntegral_norm_iff]
    simp [X]

theorem Renyi_Jensen (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : Memℒp f (ENNReal.ofReal α) (PMF.toMeasure q)) :
  ((∑' x : T, (f x) * (q x).toReal)) ^ α ≤ (∑' x : T, (f x) ^ α * (q x).toReal) := by

  conv =>
    left
    left
    right
    intro x
    rw [mul_comm]
    rw [← smul_eq_mul]
  conv =>
    right
    right
    intro x
    rw [mul_comm]
    rw [← smul_eq_mul]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := @convexOn_rpow α (le_of_lt h)
  have B : ContinuousOn (fun (x : ℝ) => x ^ α) (Set.Ici 0) := by
    apply ContinuousOn.rpow
    . exact continuousOn_id' (Set.Ici 0)
    . exact continuousOn_const
    . intro x h'
      simp at h'
      have OR : x = 0 ∨ 0 < x := by exact LE.le.eq_or_gt h'
      cases OR
      . rename_i h''
        subst h''
        right
        apply lt_trans zero_lt_one h
      . rename_i h''
        left
        by_contra
        rename_i h3
        subst h3
        simp at h''
  have C : @IsClosed ℝ UniformSpace.toTopologicalSpace (Set.Ici 0) := by
    exact isClosed_Ici
  have D := @ConvexOn.map_integral_le T ℝ t1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f (fun (x : ℝ) => x ^ α) (PMF.toMeasure.isProbabilityMeasure q) A B C
  simp at D
  apply D
  . exact MeasureTheory.ae_of_all (PMF.toMeasure q) h2
  . apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h
  . rw [Function.comp_def]
    have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h

def δ (nq : SLang U) (f : U → V) (a : V)  : {n : U | a = f n} → ENNReal := fun x : {n : U | a = f n} => nq x * (∑' (x : {n | a = f n}), nq x)⁻¹

theorem δ_normalizes (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  HasSum (δ nq f a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold δ
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.mul_inv_cancel h1 h2]

def δpmf (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) : PMF {n : U | a = f n} :=
  ⟨ δ nq f a , δ_normalizes nq f a h1 h2 ⟩

theorem δpmf_conv (nq : SLang U) (a : V) (x : {n | a = f n}) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  nq x * (∑' (x : {n | a = f n}), nq x)⁻¹ = (δpmf nq f a h1 h2) x := by
  simp [δpmf]
  conv =>
    right
    left
    left

theorem δpmf_conv' (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  (fun x : {n | a = f n} => nq x * (∑' (x : {n | a = f n}), nq x)⁻¹) = (δpmf nq f a h1 h2) := by
  ext x
  rw [δpmf_conv]

theorem witness {f : U → V} {i : V} (h : ¬{b | i = f b} = ∅) :
  ∃ x : U, i = f x := by
  rw [← nonempty_subtype]
  exact Set.nonempty_iff_ne_empty'.mpr h

theorem norm_simplify (x : ENNReal) (h : x ≠ ⊤) :
  @nnnorm ℝ SeminormedAddGroup.toNNNorm x.toReal = x := by
  simp [nnnorm]
  cases x
  . contradiction
  . rename_i v
    simp
    rfl

theorem RD1 (p q : T → ENNReal) (α : ℝ) (h : 1 < α) (RD : ∑' (x : T), p x ^ α * q x ^ (1 - α) ≠ ⊤) (nz : ∀ x : T, q x ≠ 0) (nt : ∀ x : T, q x ≠ ⊤) :
  ∑' (x : T), (p x / q x) ^ α * q x ≠ ⊤ := by
  rw [← RenyiDivergenceExpectation p q h nz nt]
  trivial

theorem ENNReal.HasSum_fiberwise {f : T → ENNReal} {a : ENNReal} (hf : HasSum f a) (g : T → V) :
    HasSum (fun c : V ↦ ∑' b : g ⁻¹' {c}, f b) a := by
  let A := (Equiv.sigmaFiberEquiv g)
  have B := @Equiv.hasSum_iff ENNReal T ((y : V) × { x // g x = y }) _ _ f a A
  replace B := B.2 hf
  have C := @HasSum.sigma ENNReal V _ _ _ _ (fun y : V => { x // g x = y }) (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) (fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) a B
  apply C
  intro b
  have F := @Summable.hasSum_iff ENNReal _ _ _ (fun c => (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) { fst := b, snd := c }) ((fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) b) _
  apply (F _).2
  . rfl
  . apply ENNReal.summable

theorem ENNReal.tsum_fiberwise (p : T → ENNReal) (f : T → V) :
  ∑' (x : V), ∑' (b : (f ⁻¹' {x})), p b
    = ∑' i : T, p i := by
  apply HasSum.tsum_eq
  apply ENNReal.HasSum_fiberwise
  apply Summable.hasSum
  exact ENNReal.summable

theorem fiberwisation (p : T → ENNReal) (f : T → V) :
 (∑' i : T, p i)
    = ∑' (x : V), if {a : T | x = f a} = {} then 0 else ∑'(i : {a : T | x = f a}), p i := by
  rw [← ENNReal.tsum_fiberwise p f]
  have A : ∀ x, f ⁻¹' {x} = { a | x = f a } := by
    intro x
    simp [Set.preimage]
    rw [Set.ext_iff]
    simp
    intro y
    exact eq_comm
  conv =>
    left
    right
    intro x
    rw [A]
  clear A
  apply tsum_congr
  intro b
  split
  . rename_i h'
    rw [h']
    simp only [tsum_empty]
  . simp

theorem convergent_subset {p : T → ENNReal} (f : T → V) (conv : ∑' (x : T), p x ≠ ⊤) :
  ∑' (x : { y : T| x = f y }), p x ≠ ⊤ := by
  rw [← condition_to_subset]
  have A : (∑' (y : T), if x = f y  then p y else 0) ≤ ∑' (x : T), p x := by
    apply tsum_le_tsum
    . intro i
      split
      . trivial
      . simp only [_root_.zero_le]
    . exact ENNReal.summable
    . exact ENNReal.summable
  rw [← lt_top_iff_ne_top]
  apply lt_of_le_of_lt A
  rw [lt_top_iff_ne_top]
  trivial

theorem ENNReal.tsum_pos {f : T → ENNReal} (h1 : ∑' x : T, f x ≠ ⊤) (h2 : ∀ x : T, f x ≠ 0) (i : T) :
  0 < ∑' x : T, f x := by
  apply (toNNReal_lt_toNNReal ENNReal.zero_ne_top h1).mp
  simp only [zero_toNNReal]
  rw [ENNReal.tsum_toNNReal_eq (ENNReal.ne_top_of_tsum_ne_top h1)]
  have S : Summable fun a => (f a).toNNReal := by
    rw [← tsum_coe_ne_top_iff_summable]
    conv =>
      left
      right
      intro b
      rw [ENNReal.coe_toNNReal (ENNReal.ne_top_of_tsum_ne_top h1 b)]
    trivial
  have B:= @NNReal.tsum_pos T (fun (a : T) => (f a).toNNReal) S i
  apply B
  apply ENNReal.toNNReal_pos (h2 i) (ENNReal.ne_top_of_tsum_ne_top h1 i)

theorem ENNReal.tsum_pos_int {f : ℤ → ENNReal} (h1 : ∑' x : ℤ, f x ≠ ⊤) (h2 : ∀ x : ℤ, f x ≠ 0) :
  0 < ∑' x : ℤ, f x := by
  apply ENNReal.tsum_pos h1 h2 42

theorem tsum_pos_int {f : ℤ → ENNReal} (h1 : ∑' x : ℤ, f x ≠ ⊤) (h2 : ∀ x : ℤ, f x ≠ 0) :
  0 < (∑' x : ℤ, f x).toReal := by
  have X : 0 = (0 : ENNReal).toReal := rfl
  rw [X]
  clear X
  apply toReal_strict_mono h1
  apply ENNReal.tsum_pos_int h1 h2

theorem DPostPocess_pre {nq : List T → SLang U} {ε₁ ε₂ : ℕ+} (h : DP nq ((ε₁ : ℝ) / ε₂)) (nn : NonZeroNQ nq) (nt : NonTopRDNQ nq) (nts : NonTopNQ nq) (conv : NonTopSum nq) (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (h2 : Neighbour l₁ l₂) :
  (∑' (x : V),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α *
        (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤
  (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by

  simp [DP, RenyiDivergence] at h

  -- Rewrite as cascading expectations
  rw [@RenyiDivergenceExpectation _ (nq l₁) (nq l₂) _ h1 (nn l₂) (nts l₂)]

  -- Shuffle the sum
  rw [fiberwisation (fun x => (nq l₁ x / nq l₂ x) ^ α * nq l₂ x) f]

  apply ENNReal.tsum_le_tsum

  intro i

  -- Get rid of elements with probability 0 in the pushforward
  split
  . rename_i empty
    rw [condition_to_subset]
    have ZE : (∑' (x_1 : ↑{n | i = f n}), nq l₁ ↑x_1) = 0 := by
      simp
      intro a H
      have I₁ : a ∈ {b | i = f b} := by
        simp [H]
      have I2 : {b | i = f b} ≠ ∅ := by
        apply ne_of_mem_of_not_mem' I₁
        simp
      contradiction
    rw [ZE]
    simp only [toReal_mul, zero_toReal, ge_iff_le]

    rw [ENNReal.zero_rpow_of_pos]
    . simp
    . apply lt_trans zero_lt_one h1

  -- Part 2: apply Jensen's inequality
  . rename_i NotEmpty

    have MasterRW : ∀ l : List T, ∑' (a : ↑{a | i = f a}), nq l ↑a ≠ ⊤ := by
      intro l
      apply convergent_subset
      simp [NonTopSum] at conv
      have conv := conv l
      apply conv

    have MasterZero : ∀ l : List T, ∑' (a : ↑{a | i = f a}), nq l ↑a ≠ 0 := by
      intro l
      simp
      have T := witness NotEmpty
      cases T
      rename_i z w
      exists z
      constructor
      . trivial
      . apply nn l

    have S2 : (∑' (a : ↑{n | i = f n}), nq l₁ ↑a / nq l₂ ↑a * (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂)) a) ^ α ≠ ⊤ := by
      conv =>
        left
        left
        right
        intro a
        rw [← δpmf_conv]
        rw [division_def]
        rw [mul_assoc]
        right
        rw [← mul_assoc]
        rw [ENNReal.inv_mul_cancel (nn l₂ a) (nts l₂ a)]
      rw [one_mul]
      rw [ENNReal.tsum_mul_right]
      apply ENNReal.rpow_ne_top_of_nonneg (le_of_lt (lt_trans zero_lt_one h1 ))
      apply mul_ne_top
      . apply convergent_subset _ (conv l₁)
      . apply inv_ne_top.mpr (MasterZero l₂)

    have S1 : ∀ (a : ↑{n | i = f n}), nq l₁ ↑a / nq l₂ ↑a * (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂)) a ≠ ⊤ := by
      intro a
      apply mul_ne_top
      . rw [division_def]
        apply mul_ne_top (nts l₁ a)
        apply inv_ne_top.mpr (nn l₂ a)
      . rw [← δpmf_conv]
        apply mul_ne_top (nts l₂ a)
        apply inv_ne_top.mpr (MasterZero l₂)

    have S3 : ∑' (a : ↑{n | i = f n}), (nq l₁ ↑a / nq l₂ ↑a) ^ α * (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂)) a ≠ ⊤ := by
      conv =>
        left
        right
        intro a
        rw [← δpmf_conv]
        rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      apply mul_ne_top
      . rw [← RenyiDivergenceExpectation _ _ h1]
        . replace nt := nt α h1 l₁ l₂ h2
          apply convergent_subset _ nt
        . intro x
          apply nn
        . intro x
          apply nts
      . apply inv_ne_top.mpr (MasterZero l₂)

    have S4 : ∀ (a : ↑{n | i = f n}), (nq l₁ ↑a / nq l₂ ↑a) ^ α * (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂)) a ≠ ⊤ := by
      intro a
      apply ENNReal.ne_top_of_tsum_ne_top S3

    rw [condition_to_subset]
    rw [condition_to_subset]

    -- Introduce Q(f⁻¹ i)
    let κ := ∑' x : {n : U | i = f n}, nq l₂ x
    have P4 : κ / κ = 1 := by
      rw [division_def]
      rw [ENNReal.mul_inv_cancel]
      . simp [κ]  -- Use here for δ normalization
        have T := witness NotEmpty
        cases T
        rename_i z w
        exists z
        constructor
        . trivial
        . apply nn l₂
      . simp only [κ]
        apply MasterRW l₂

    conv =>
      right
      right
      intro a
      rw [← mul_one ((nq l₁ ↑a / nq l₂ ↑a) ^ α * nq l₂ ↑a)]
      right
      rw [← P4]
    clear P4
    simp only [κ]

    conv =>
      right
      right
      intro a
      right
      rw [division_def]
      rw [mul_comm]

    conv =>
      right
      right
      intro a
      rw [← mul_assoc]

    rw [ENNReal.tsum_mul_right]

    -- Jensen's inequality

    have P5 : ∀ (x : ↑{n | i = f n}), 0 ≤ (fun a => (nq l₁ ↑a / nq l₂ ↑a).toReal) x := by
      intro x
      simp only [toReal_nonneg]

    have XXX : @Memℒp ℝ Real.normedAddCommGroup (↑{n | i = f n}) Subtype.instMeasurableSpace (fun a => (nq l₁ ↑a / nq l₂ ↑a).toReal)
      (ENNReal.ofReal α) (PMF.toMeasure (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂))) := by
      simp [Memℒp]
      constructor
      . apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
        apply Measurable.stronglyMeasurable
        apply Measurable.ennreal_toReal
        conv =>
          right
          intro x
          rw [division_def]
        apply Measurable.mul
        . -- MeasurableSingletonClass.toDiscreteMeasurableSpace
          apply measurable_discrete
        . apply Measurable.inv
          apply measurable_discrete
      . simp [snorm]
        split
        . simp
        . simp [snorm']
          rw [MeasureTheory.lintegral_countable'] -- Uses countable
          rw [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h1))]
          have OTHER : ∀ a, nq l₁ a / nq l₂ a ≠ ⊤ := by
            intro a
            rw [division_def]
            rw [ne_iff_lt_or_gt]
            left
            rw [mul_lt_top_iff]
            left
            constructor
            . exact Ne.lt_top' (id (Ne.symm (nts l₁ a)))
            . simp
              exact pos_iff_ne_zero.mpr (nn l₂ a)

          conv =>
            left
            left
            right
            intro a
            rw [norm_simplify _ (OTHER a)]
          have Z : 0 < α⁻¹ := by
            simp
            apply lt_trans zero_lt_one h1
          rw [rpow_lt_top_iff_of_pos Z]
          conv =>
            left
            right
            intro a
            rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

          apply Ne.lt_top' (id (Ne.symm _))
          apply S3


    have Jensen's := @Renyi_Jensen {n : U | i = f n} Subtype.instMeasurableSpace Subtype.instMeasurableSingletonClass (fun a => (nq l₁ a / nq l₂ a).toReal) (δpmf (nq l₂) f i (MasterZero l₂) (MasterRW l₂)) α h1 P5 XXX
    clear P5

    have P6 : 0 ≤ (∑' (x : ↑{n | i = f n}), nq l₂ ↑x).toReal := by
      simp only [toReal_nonneg]
    have A' := mul_le_mul_of_nonneg_left Jensen's P6
    clear Jensen's P6

    conv =>
      right
      rw [mul_comm]
      right
      right
      intro a
      rw [mul_assoc]
      rw [δpmf_conv]

    -- Here

    replace A' := ofReal_le_ofReal A'
    rw [ofReal_mul toReal_nonneg] at A'
    rw [ofReal_mul toReal_nonneg] at A'
    rw [ofReal_toReal_eq_iff.2 (MasterRW l₂)] at A'
    simp only at A'

    revert A'
    conv =>
      left
      right
      right
      right
      right
      intro x
      rw [toReal_rpow]
      rw [← toReal_mul]
    conv =>
      left
      right
      right
      right
      rw [← ENNReal.tsum_toReal_eq S4]
    intro A'
    rw [ofReal_toReal_eq_iff.2 S3] at A'

    apply le_trans _ A'
    clear A'
    apply le_of_eq

    -- Part 3:

    conv =>
      right
      right
      right
      left
      right
      intro x
      rw [← toReal_mul]
    rw [← ENNReal.tsum_toReal_eq S1]
    rw [toReal_rpow]
    rw [ofReal_toReal_eq_iff.2 S2]

    conv =>
      right
      right
      left
      right
      intro x
      rw [division_def]
      rw [← δpmf_conv]
      rw [mul_assoc]
      right
      rw [← mul_assoc]
      left
      rw [ENNReal.inv_mul_cancel (nn l₂ x) (nts l₂ x)]
    simp only [one_mul]

    rw [ENNReal.tsum_mul_right]
    have H4 : (∑' (a : ↑{a | i = f a}), nq l₂ ↑a)⁻¹ ≠ ⊤ := by
      apply inv_ne_top.mpr
      simp
      have T := witness NotEmpty
      cases T
      rename_i z w
      exists z
      constructor
      . trivial
      . apply nn l₂
    rw [ENNReal.mul_rpow_of_ne_top (MasterRW l₁) H4]

    have H3 : ∑' (a : ↑{a | i = f a}), nq l₂ ↑a ≠ 0 := by
      simp
      have T := witness NotEmpty
      cases T
      rename_i z w
      exists z
      constructor
      . trivial
      . apply nn l₂
    rw [ENNReal.rpow_sub _ _ H3 (MasterRW l₂)]
    rw [ENNReal.rpow_one]
    rw [division_def]
    rw [← mul_assoc]
    rw [← mul_assoc]
    congr 1
    . rw [mul_comm]
    . congr 1
      rw [ENNReal.inv_rpow]

theorem tsum_ne_zero_of_ne_zero {T : Type} [Inhabited T] (f : T → ENNReal) (h : ∀ x : T, f x ≠ 0) :
  ∑' x : T, f x ≠ 0 := by
  by_contra CONTRA
  rw [ENNReal.tsum_eq_zero] at CONTRA
  have A := h default
  have B := CONTRA default
  contradiction

theorem DPPostProcess {nq : List T → SLang U} {ε₁ ε₂ : ℕ+} (h : DP nq ((ε₁ : ℝ) / ε₂)) (nn : NonZeroNQ nq) (nt : NonTopRDNQ nq) (nts : NonTopNQ nq) (conv : NonTopSum nq) (f : U → V) :
  DP (PostProcess nq f) ((ε₁ : ℝ) / ε₂) := by
  simp [PostProcess, DP, RenyiDivergence]
  intro α h1 l₁ l₂ h2
  have h' := h
  simp [DP, RenyiDivergence] at h'
  replace h' := h' α h1 l₁ l₂ h2

  -- Part 1, removing fluff

  apply le_trans _ h'
  clear h'

  -- remove the α scaling
  have A : 0 ≤ (α - 1)⁻¹ := by
    simp
    apply le_of_lt h1
  apply mul_le_mul_of_nonneg_left _ A
  clear A

  have RDConvegence : ∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α) ≠ ⊤ := by
    simp [NonTopRDNQ] at nt
    have nt := nt α h1 l₁ l₂ h2
    trivial

  have B := DPostPocess_pre h nn nt nts conv f h1 h2
  have B' : ∑' (x : V), (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α * (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α) ≠ ⊤ := by
    by_contra CONTRA
    rw [CONTRA] at B
    simp at B
    contradiction

  -- remove the log
  apply log_le_log _ (toReal_mono RDConvegence B)
  apply toReal_pos _ B'
  apply (tsum_ne_zero_iff ENNReal.summable).mpr
  exists (f default)

  rw [ENNReal.tsum_eq_add_tsum_ite default]
  conv =>
    left
    right
    rw [ENNReal.tsum_eq_add_tsum_ite default]
  simp only [reduceIte]
  apply mul_ne_zero
  . by_contra CONTRA
    rw [ENNReal.rpow_eq_zero_iff_of_pos (lt_trans zero_lt_one h1)] at CONTRA
    simp at CONTRA
    cases CONTRA
    rename_i left right
    have Y := nn l₁ default
    contradiction
  . by_contra CONTRA
    rw [ENNReal.rpow_eq_zero_iff] at CONTRA
    cases CONTRA
    . rename_i CONTRA
      cases CONTRA
      rename_i left right
      simp at left
      cases left
      rename_i le1 le2
      have Y := nn l₂ default
      contradiction
    . rename_i CONTRA
      cases CONTRA
      rename_i left right
      simp at left
      cases left
      . rename_i left
        have Y := nts l₂ default
        contradiction
      . rename_i left
        have Rem := conv l₂
        have X : (∑' (x : U), if x = default then 0 else if f default = f x then nq l₂ x else 0) ≤ ∑' (n : U), nq l₂ n := by
          apply ENNReal.tsum_le_tsum
          intro a
          split
          . simp
          . split
            . simp
            . simp
        replace Rem := Ne.symm Rem
        have Y := Ne.lt_top' Rem
        have Z : (∑' (x : U), if x = default then 0 else if f default = f x then nq l₂ x else 0) < ⊤ := by
          apply lt_of_le_of_lt X Y
        rw [lt_top_iff_ne_top] at Z
        contradiction

theorem DPPostPRocess_NonZeroNQ {nq : List T → SLang U} {f : U → V} (nn : NonZeroNQ nq) (sur : Function.Surjective f) :
  NonZeroNQ (PostProcess nq f) := by
  simp [NonZeroNQ, Function.Surjective, PostProcess] at *
  intros l n
  replace sur := sur n
  cases sur
  rename_i a h
  exists a
  constructor
  . rw [h]
  . apply nn

theorem DPPostPRocess_NonTopSum {nq : List T → SLang U} (f : U → V) (nt : NonTopSum nq) (sur : Function.Surjective f) :
  NonTopSum (PostProcess nq f) := by
  simp [NonTopSum, PostProcess] at *
  intros l
  have nt := nt l
  rw [← ENNReal.tsum_fiberwise _ f] at nt
  conv =>
    right
    left
    right
    intro n
    rw [condition_to_subset]
  unfold Set.preimage at nt
  sorry -- looks good

theorem DPPostProcess_NonTopRDNQ {nq : List T → SLang U} (f : U → V) (nt : NonTopRDNQ nq) (ns : NonTopSum nq) (sur : Function.Surjective f) :
  NonTopRDNQ (PostProcess nq f) := by
  simp [NonTopRDNQ, NonTopSum, PostProcess] at *
  intros α h1 l₁ l₂ h2
  replace nt := nt α h1 l₁ l₂ h2
  have ns1 := ns l₁
  have ns2 := ns l₂
  sorry -- probably good but tedious work

theorem zCDPPostProcess (nq : List T → SLang U) (ε₁ ε₂ : ℕ+) (f : U → V) (sur : Function.Surjective f) (h : zCDP nq ((ε₁ : ℝ) / ε₂)) :
  zCDP (PostProcess nq f) (((ε₁ : ℝ) / ε₂)) := by
  simp [zCDP] at *
  cases h ; rename_i h1 h2 ; cases h2 ; rename_i h2 h3 ; cases h3 ; rename_i h3 h4 ; cases h4 ; rename_i h4 h5
  repeat any_goals constructor
  . apply DPPostProcess h1 h2 h5 h4 h3
  . apply DPPostPRocess_NonZeroNQ h2 sur
  . sorry
  . sorry
  . sorry

end SLang
