/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.DiffPrivacy.ConcentratedBound
import SampCert.SLang
import SampCert.Samplers.GaussianGen.Basic
import SampCert.DiffPrivacy.Neighbours
import SampCert.DiffPrivacy.Sensitivity
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory

def DP (q : List T → SLang U) (ε : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence (q l₁) (q l₂) α ≤ (1/2) * ε ^ 2 * α

def NonZeroNQ (nq : List T → SLang U) :=
  ∀ l : List T, ∀ n : U, nq l n ≠ 0

def NonTopNQ (nq : List T → SLang U) :=
  ∀ l : List T, ∀ n : U, nq l n ≠ ⊤

def NonTopRDNQ (nq : List T → SLang U) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  ∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α) ≠ ⊤

namespace SLang

def NoisedQuery (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  DiscreteGaussianGenSample (Δ * ε₂) ε₁ (query l)

theorem NoisedQueryDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (NoisedQuery query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  simp [DP, NoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @DiscreteGaussianGenSampleZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A
  replace bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  ring_nf
  simp
  conv =>
    left
    left
    right
    rw [mul_pow]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [← mul_assoc]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [← mul_assoc]
  simp only [inv_pow]
  rw [mul_inv_le_iff']
  . have A : (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := le_refl (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹)
    have B : 0 ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := by
      simp
      apply @le_trans ℝ _ 0 1 α (instStrictOrderedCommRingReal.proof_3) (le_of_lt h1)
    apply mul_le_mul A _ _ B
    . apply sq_le_sq.mpr
      simp only [abs_cast]
      rw [← Int.cast_sub]
      rw [← Int.cast_abs]
      apply Int.cast_le.mpr
      rw [← Int.natCast_natAbs]
      apply Int.ofNat_le.mpr
      trivial
    . apply sq_nonneg
  . rw [pow_two]
    rw [_root_.mul_pos_iff]
    left
    simp

theorem NoisedQuery_NonZeroNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonZeroNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonZeroNQ, NoisedQuery, DiscreteGaussianGenSample]
  intros l n
  exists (n - query l)
  simp
  have A : ((Δ : ℝ) * ε₂ / ε₁) ≠ 0 := by
    simp
  have X := @discrete_gaussian_pos (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) A 0 (n - query l)
  simp at X
  trivial

theorem NoisedQuery_NonTopNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonTopNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonTopNQ, NoisedQuery, DiscreteGaussianGenSample]
  intro l n
  rw [ENNReal.tsum_eq_add_tsum_ite (n - query l)]
  simp
  have X : ∀ x : ℤ, (@ite ℝ≥0∞ (x = n - query l) (propDecidable (x = n - query l)) 0
    (@ite ℝ≥0∞ (n = x + query l) (instDecidableEqInt n (x + query l))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x)) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  conv =>
    right
    left
    right
    intro x
    rw [X]
  simp

theorem discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  . simp [gauss_term_ℝ]
    congr 3
    ring_nf
  . rw [SG_periodic h]

theorem NoisedQuery_NonTopRDNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonTopRDNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonTopRDNQ, NoisedQuery, DiscreteGaussianGenSample]
  intro α _ l₁ l₂ _
  have A : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₁) (propDecidable (x_1 = x - query l₁)) 0
  (@ite ℝ≥0∞ (x = x_1 + query l₁) (instDecidableEqInt x (x_1 + query l₁))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0 )) = 0 := by
    intro x y
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  have B : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₂) (propDecidable (x_1 = x - query l₂)) 0
    (@ite ℝ≥0∞ (x = x_1 + query l₂) (instDecidableEqInt x (x_1 + query l₂))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0)) = 0 := by
    intro x y
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  conv =>
    right
    left
    right
    intro x
    left
    rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₁)]
    simp
    left
    right
    right
    intro y
    rw [A]
  simp
  conv =>
    right
    left
    right
    intro x
    right
    rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₂)]
    simp
    left
    right
    right
    intro y
    rw [B]
  simp
  clear A B
  have P : (Δ : ℝ) * ε₂ / ε₁ ≠ 0 := by
    simp
  have A : ∀ x : ℤ, ∀ l : List T, 0 < discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l)) := by
    intro x l
    have A' := @discrete_gaussian_pos _ P 0 (x - query l)
    simp at A'
    trivial
  have B : ∀ x : ℤ, 0 ≤ discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l₁)) ^ α := by
    intro x
    have A' := @discrete_gaussian_nonneg _ P 0 (x - query l₁)
    simp at A'
    apply rpow_nonneg A'
  conv =>
    right
    left
    right
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (A x l₁)]
    rw [ENNReal.ofReal_rpow_of_pos (A x l₂)]
    rw [← ENNReal.ofReal_mul (B x)]
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  . simp
  . intro n
    have X := @RenyiSumSG_nonneg _ α P (query l₁) (query l₂) n
    rw [discrete_gaussian_shift P]
    rw [discrete_gaussian_shift P]
    simp [X]
  . have X := @SummableRenyiGauss _ P (query l₁) (query l₂)
    conv =>
      right
      intro x
      rw [discrete_gaussian_shift P]
      rw [discrete_gaussian_shift P]
    simp [X]

def Compose (nq1 nq2 : List T → SLang ℤ) (l : List T) : SLang (ℤ × ℤ) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

theorem ENNReal_toTeal_NZ (x : ENNReal) (h1 : x ≠ 0) (h2 : x ≠ ⊤) :
  x.toReal ≠ 0 := by
  unfold ENNReal.toReal
  unfold ENNReal.toNNReal
  simp
  intro H
  cases H
  . contradiction
  . contradiction

theorem simp_α_1 {α : ℝ} (h : 1 < α) : 0 < α := by
  apply @lt_trans _ _ _ 1 _ _ h
  simp only [zero_lt_one]

theorem RenyiNoisedQueryNonZero {nq : List T → SLang ℤ} {α ε : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (h2 : Neighbour l₁ l₂) (h3 : DP nq ε) (h4 : NonZeroNQ nq) (h5 : NonTopRDNQ nq) (nts : NonTopNQ nq) :
  (∑' (i : ℤ), nq l₁ i ^ α * nq l₂ i ^ (1 - α)).toReal ≠ 0 := by
  simp [DP] at h3
  replace h3 := h3 α h1 l₁ l₂ h2
  simp [RenyiDivergence] at h3
  simp [NonZeroNQ] at h4
  simp [NonTopRDNQ] at h5
  replace h5 := h5 α h1 l₁ l₂ h2
  have h6 := h4 l₁
  have h7 := h4 l₂
  apply ENNReal_toTeal_NZ
  . by_contra CONTRA
    rw [ENNReal.tsum_eq_zero] at CONTRA
    replace CONTRA := CONTRA 42
    replace h6 := h6 42
    replace h7 := h7 42
    rw [_root_.mul_eq_zero] at CONTRA
    cases CONTRA
    . rename_i h8
      rw [rpow_eq_zero_iff_of_pos] at h8
      contradiction
      apply simp_α_1 h1
    . rename_i h8
      rw [ENNReal.rpow_eq_zero_iff] at h8
      cases h8
      . rename_i h8
        cases h8
        contradiction
      . rename_i h8
        cases h8
        rename_i h8 h9
        replace nts := nts l₂ 42
        contradiction
  . exact h5

theorem compose_sum_rw (nq1 nq2 : List T → SLang ℤ) (b c : ℤ) (l : List T) :
  (∑' (a : ℤ), nq1 l a * ∑' (a_1 : ℤ), if b = a ∧ c = a_1 then nq2 l a_1 else 0) = nq1 l b * nq2 l c := by
  have A : ∀ a b : ℤ, (∑' (a_1 : ℤ), if b = a ∧ c = a_1 then nq2 l a_1 else 0) = if b = a then (∑' (a_1 : ℤ), if c = a_1 then nq2 l a_1 else 0) else 0 := by
    intro x  y
    split
    . rename_i h
      subst h
      simp
    . rename_i h
      simp
      intro h
      contradiction
  conv =>
    left
    right
    intro a
    right
    rw [A]
  rw [ENNReal.tsum_eq_add_tsum_ite b]
  simp
  have B : ∀ x : ℤ, (@ite ℝ≥0∞ (x = b) (instDecidableEqInt x b) 0
    (@ite ℝ≥0∞ (b = x) (instDecidableEqInt b x) (nq1 l x * ∑' (a_1 : ℤ), @ite ℝ≥0∞ (c = a_1) (instDecidableEqInt c a_1) (nq2 l a_1) 0) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [B]
  simp
  congr 1
  rw [ENNReal.tsum_eq_add_tsum_ite c]
  simp
  have C :∀ x : ℤ,  (@ite ℝ≥0∞ (x = c) (propDecidable (x = c)) 0 (@ite ℝ≥0∞ (c = x) (instDecidableEqInt c x) (nq2 l x) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro X
    rw [C]
  simp

theorem DPCompose {nq1 nq2 : List T → SLang ℤ} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : DP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : DP nq2 ((ε₃ : ℝ) / ε₄)) (nn1 : NonZeroNQ nq1) (nn2 : NonZeroNQ nq2) (nt1 : NonTopRDNQ nq1) (nt2 : NonTopRDNQ nq2) (nts1 : NonTopNQ nq1) (nts2 : NonTopNQ nq2) :
  DP (Compose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [Compose, RenyiDivergence, DP]
  intro α h3 l₁ l₂ h4
  have X := h1
  have Y := h2
  simp [DP] at h1 h2
  replace h1 := h1 α h3 l₁ l₂ h4
  replace h2 := h2 α h3 l₁ l₂ h4
  simp [RenyiDivergence] at h1 h2
  rw [tsum_prod' ENNReal.summable (fun b : ℤ => ENNReal.summable)]
  . simp
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [compose_sum_rw]
      rw [compose_sum_rw]
      rw [ENNReal.mul_rpow_of_ne_zero (nn1 l₁ b) (nn2 l₁ c)]
      rw [ENNReal.mul_rpow_of_ne_zero (nn1 l₂ b) (nn2 l₂ c)]
      rw [mul_assoc]
      right
      rw [mul_comm]
      rw [mul_assoc]
      right
      rw [mul_comm]
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [← mul_assoc]
    conv =>
      left
      right
      right
      right
      right
      intro b
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
    rw [ENNReal.toReal_mul]
    rw [Real.log_mul]
    . rw [mul_add]
      have D := _root_.add_le_add h1 h2
      apply le_trans D
      rw [← add_mul]
      rw [mul_le_mul_iff_of_pos_right]
      . rw [← mul_add]
        rw [mul_le_mul_iff_of_pos_left]
        . ring_nf
          simp
        . simp
      . apply lt_trans zero_lt_one h3
    . apply RenyiNoisedQueryNonZero h3 h4 X nn1 nt1 nts1
    . apply RenyiNoisedQueryNonZero h3 h4 Y nn2 nt2 nts2

theorem DPCompose_NonZeroNQ {nq1 nq2 : List T → SLang ℤ} (nn1 : NonZeroNQ nq1) (nn2 : NonZeroNQ nq2) :
  NonZeroNQ (Compose nq1 nq2) := by
  simp [NonZeroNQ] at *
  intro l a b
  replace nn1 := nn1 l a
  replace nn2 := nn2 l b
  simp [Compose]
  exists a
  simp
  intro H
  cases H
  . rename_i H
    contradiction
  . rename_i H
    contradiction

theorem DPCompose_NonTopNQ {nq1 nq2 : List T → SLang ℤ} (nt1 : NonTopNQ nq1) (nt2 : NonTopNQ nq2) :
  NonTopNQ (Compose nq1 nq2) := by
  simp [NonTopNQ] at *
  intro l a b
  replace nt1 := nt1 l a
  replace nt2 := nt2 l b
  simp [Compose]
  rw [compose_sum_rw]
  rw [mul_eq_top]
  intro H
  cases H
  . rename_i H
    cases H
    contradiction
  . rename_i H
    cases H
    contradiction

theorem DPCompose_NonTopRDNQ {nq1 nq2 : List T → SLang ℤ} (nt1 : NonTopRDNQ nq1) (nt2 : NonTopRDNQ nq2) (nn1 : NonZeroNQ nq1) (nn2 : NonZeroNQ nq2) :
  NonTopRDNQ (Compose nq1 nq2) := by
  simp [NonTopRDNQ] at *
  intro α h1 l₁ l₂ h2
  replace nt1 := nt1 α h1 l₁ l₂ h2
  replace nt2 := nt2 α h1 l₁ l₂ h2
  simp [Compose]
  rw [ENNReal.tsum_prod']
  simp
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    congr
    . left
      rw [compose_sum_rw]
    . left
      rw [compose_sum_rw]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [ENNReal.mul_rpow_of_ne_zero (nn1 l₁ x) (nn2 l₁ y)]
    rw [ENNReal.mul_rpow_of_ne_zero (nn1 l₂ x) (nn2 l₂ y)]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    right
    rw [mul_comm]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [← mul_assoc]
  conv =>
    right
    left
    right
    intro x
    rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
  intro H
  rw [mul_eq_top] at H
  cases H
  . rename_i h3
    cases h3
    rename_i h4 h5
    contradiction
  . rename_i h3
    cases h3
    rename_i h4 h5
    contradiction

def PostProcess (nq : List T → SLang U) (pp : U → ℤ) (l : List T) : SLang ℤ := do
  let A ← nq l
  return pp A

theorem foo (f : U → ℤ) (g : U → ENNReal) (x : ℤ) :
  (∑' a : U, if x = f a then g a else 0) = ∑' a : { a | x = f a }, g a := by
  have A := @tsum_split_ite U (fun a : U => x = f a) g (fun _ => 0)
  simp only [decide_eq_true_eq, tsum_zero, add_zero] at A
  rw [A]
  have B : ↑{i | decide (x = f i) = true} = ↑{a | x = f a} := by
    simp
  rw [B]

variable {T : Type}
variable [m1 : MeasurableSpace T]
variable [m2 : MeasurableSingletonClass T]
variable [m3: MeasureSpace T]

theorem Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal) (mem : Memℒp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤)  :
  MeasureTheory.Integrable (fun x : T => (f x) ^ α.toReal) μ := by
  have X := @MeasureTheory.Memℒp.integrable_norm_rpow T ℝ m1 μ _ f α mem h1 h2
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

theorem bar (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : Memℒp f (ENNReal.ofReal α) (PMF.toMeasure q)) :
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
  have D := @ConvexOn.map_integral_le T ℝ m1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f (fun (x : ℝ) => x ^ α) (PMF.toMeasure.isProbabilityMeasure q) A B C
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
    have Z := @Integrable_rpow T m1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T m1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h

theorem quux (f : U → ℤ) (g : U → ENNReal) :
  (∑' (x : ℤ) (i : ↑{a | x = f a}), g i)
    = ∑' i : U, g i := by
  sorry

variable {U : Type}
variable [m2 : MeasurableSpace U] [m2' : MeasurableSingletonClass U]

def δ (nq : SLang U) (f : U → ℤ) (a : ℤ)  : {n : U | a = f n} → ENNReal := fun x : {n : U | a = f n} => nq x * (∑' (x : {n | a = f n}), nq x)⁻¹

theorem δ_normalizes (nq : SLang U) (f : U → ℤ) (a : ℤ) :
  HasSum (δ nq f a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold δ
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.mul_inv_cancel]
  . simp
    sorry -- ∃ x, a = f x ∧ ¬nq x = 0
  . sorry -- ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤

def δpmf (nq : SLang U) (f : U → ℤ) (a : ℤ) : PMF {n : U | a = f n} :=
  ⟨ δ nq f a , δ_normalizes nq f a ⟩

theorem δpmf_conv (nq : List T → SLang U) (a : ℤ) (x : {n | a = f n}) :
  nq l₂ x * (∑' (x : {n | a = f n}), nq l₂ x)⁻¹ = (δpmf (nq l₂) f a) x := by
  simp [δpmf]
  conv =>
    right
    left
    left

theorem preparation {nq : List T → SLang U} (nn : NonZeroNQ nq) (nt : NonTopRDNQ nq) (nts : NonTopNQ nq) (f : U → ℤ) {α : ℝ} (h1 : 1 < α) (mem : ∀ (a : ℤ),
  Memℒp (fun a_1 : {n | a = f n} => (nq l₁ ↑a_1 / nq l₂ ↑a_1).toReal) (ENNReal.ofReal α) (PMF.toMeasure (δpmf (nq l₂) f a))):
   (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)).toReal
    ≥
      (∑' (x : ℤ),
        (∑' (x_1 : ↑{n | x = f n}), nq l₂ ↑x_1).toReal *
          (∑' (x_1 : ↑{n | x = f n}), (nq l₁ ↑x_1 / nq l₂ ↑x_1).toReal * ((δpmf (nq l₂) f x) x_1).toReal) ^ α)
     := by

  have X₁ : ∀ (x : U), nq l₂ x ≠ 0 := by
    intro x
    apply nn l₂ x
  have X₂ : ∀ (x : U), nq l₂ x ≠ ⊤ := by
    intro x
    apply nts l₂ x

  rw [@RenyiDivergenceExpectation _ (nq l₁) (nq l₂) _ h1 X₁ X₂]
  clear X₁ X₂

  rw [← quux f (fun x => (nq l₁ x / nq l₂ x) ^ α * nq l₂ x)]

  have P1 : ∀ (a : ℤ), ∑' (i : ↑{a_1 | a = f a_1}), (nq l₁ ↑i / nq l₂ ↑i) ^ α * nq l₂ ↑i ≠ ⊤ := sorry
  have P2 : ∀ (a : ℤ), ∀ (a_1 : ↑{a_1 | a = f a_1}), (nq l₁ ↑a_1 / nq l₂ ↑a_1) ^ α * nq l₂ ↑a_1 ≠ ⊤ := sorry

  rw [ENNReal.tsum_toReal_eq P1]
  conv =>
    left
    right
    intro a
    rw [ENNReal.tsum_toReal_eq (P2 a)]
    right
    intro b
    rw [toReal_mul]

  -- have P3 : (∀ (x : U), 0 ≤ (fun a => (nq l₁ a / nq l₂ a).toReal) x) := by
  --   intro x
  --   simp only [toReal_nonneg]

  let κ (a : ℤ) := ∑' x : {n : U | a = f n}, nq l₂ x
  have P4 : ∀ n : ℤ, (κ n / κ n).toReal = 1 := by
    intro n
    rw [division_def]
    rw [ENNReal.mul_inv_cancel]
    . rw [one_toReal]
    . simp [κ]
      sorry -- ∃ x, n = f x ∧ ¬nq l₂ x = 0
    . simp only [κ]
      sorry -- ∑' (x : ↑{n_1 | n = f n_1}), nq l₂ ↑x ≠ ⊤

  conv =>
    left
    right
    intro a
    rw [← mul_one (∑' (b : ↑{a_1 | a = f a_1}), ((nq l₁ ↑b / nq l₂ ↑b) ^ α).toReal * (nq l₂ ↑b).toReal)]
    right
    rw [← (P4 a)]
    rw [toReal_div]

  conv =>
    left
    right
    intro a
    rw [division_def]
    right
    rw [mul_comm]

  conv =>
    left
    right
    intro a
    rw [← mul_assoc]
    rw [← tsum_mul_right]
    left
    right
    intro x
    rw [mul_assoc]
    right
    rw [← toReal_inv]
    rw [← toReal_mul]

  simp only [κ]

  have P5 : ∀ a : ℤ, ∀ (x : ↑{n | a = f n}), 0 ≤ (nq l₁ ↑x / nq l₂ ↑x).toReal := by
    intro a x
    simp only [toReal_nonneg]

  have A := fun a : ℤ => @bar {n : U | a = f n} Subtype.instMeasurableSpace Subtype.instMeasurableSingletonClass (fun a => (nq l₁ a / nq l₂ a).toReal) (δpmf (nq l₂) f a) α h1 (P5 a) (mem a)
  have P6 : ∀ a, 0 ≤ (∑' (x : ↑{n | a = f n}), nq l₂ ↑x).toReal := by
    intro a
    simp only [toReal_nonneg]
  have A' := fun a : ℤ => mul_le_mul_of_nonneg_left (A a) (P6 a)
  clear A P6

  have Y₁ : Summable fun i =>
    (∑' (x : ↑{n | i = f n}), nq l₂ ↑x).toReal *
      (∑' (x : ↑{n | i = f n}), (nq l₁ ↑x / nq l₂ ↑x).toReal * ((δpmf (nq l₂) f i) x).toReal) ^ α := sorry

  have Y₂ : Summable fun i =>
    (∑' (x : ↑{n | i = f n}), nq l₂ ↑x).toReal *
      ∑' (x : ↑{n | i = f n}), (nq l₁ ↑x / nq l₂ ↑x).toReal ^ α * ((δpmf (nq l₂) f i) x).toReal := sorry

  have B := tsum_le_tsum A' Y₁ Y₂
  clear A'
  clear Y₁ Y₂

  conv =>
    left
    right
    intro a
    left
    right
    intro x
    rw [δpmf_conv]

  conv =>
    left
    right
    intro a
    rw [mul_comm]
    right
    right
    intro x
    left
    rw [← toReal_rpow]

  simp only [ge_iff_le]
  exact B

theorem DPPostProcess {nq : List T → SLang U} {ε₁ ε₂ : ℕ+} (h : DP nq ((ε₁ : ℝ) / ε₂)) (nn : NonZeroNQ nq) (nt : NonTopRDNQ nq) (nts : NonTopNQ nq) (f : U → ℤ) :
  DP (PostProcess nq f) ((ε₁ : ℝ) / ε₂) := by
  simp [PostProcess, DP, RenyiDivergence]
  intro α h1 l₁ l₂ h2
  simp [DP, RenyiDivergence] at h
  replace h := h α h1 l₁ l₂ h2

  apply le_trans _ h
  clear h

  have A : 0 ≤ (α - 1)⁻¹ := by
    simp
    apply le_of_lt h1
  apply mul_le_mul_of_nonneg_left _ A
  clear A
  have B : 0 <
  (∑' (x : ℤ),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α * (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)).toReal := sorry
  apply log_le_log B
  clear B

  have C := @preparation _ _ _ _ l₁ l₂ nq nn nt nts f α h1 sorry

  apply le_trans _ C
  clear C
  apply le_of_eq

  rw [ENNReal.tsum_toReal_eq sorry]
  apply tsum_congr
  intro b
  rw [foo]
  rw [foo]
  rw [toReal_mul]
  conv =>
    right
    right
    left
    right
    intro x
    rw [division_def]
    rw [toReal_mul]
    rw [← δpmf_conv]
    rw [toReal_mul]
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [← toReal_mul]
    rw [ENNReal.inv_mul_cancel (nn l₂ x) (nts l₂ x)]
    rw [one_toReal]
  simp only [one_mul]

  rw [tsum_mul_right]
  rw [Real.mul_rpow sorry sorry]

  rw [ENNReal.rpow_sub _ _ sorry sorry]
  rw [ENNReal.rpow_one]
  rw [division_def]
  rw [toReal_mul]
  rw [← toReal_rpow]
  rw [← mul_assoc]
  rw [← mul_assoc]
  congr 1
  . rw [mul_comm]
    congr 2
    rw [ENNReal.tsum_toReal_eq sorry]
  . rw [toReal_rpow]
    congr 1
    rw [ENNReal.inv_rpow]










end SLang
