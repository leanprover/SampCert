/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# Postprocessing

This file proves zCDP for ``privPostProcess``.
-/

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

lemma Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal) (mem : Memℒp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤)  :
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

/--
Jensen's ineuquality for the exponential applied to Renyi's sum
-/
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

lemma δ_normalizes (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
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
  rfl

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

-- theorem RD1 (p q : T → ENNReal) (α : ℝ) (h : 1 < α) (RD : ∑' (x : T), p x ^ α * q x ^ (1 - α) ≠ ⊤) (nz : ∀ x : T, q x ≠ 0) (nt : ∀ x : T, q x ≠ ⊤) :
--   ∑' (x : T), (p x / q x) ^ α * q x ≠ ⊤ := by
--   rw [← RenyiDivergenceExpectation p q h nz nt]
--   trivial

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


-- set_option pp.coercions false

theorem DPostPocess_pre_reduct {nq : List T → SLang U} {HNorm : ∀ l, HasSum (nq l) 1} {ε₁ ε₂ : ℕ+}
  (h : zCDPBound nq HNorm ((ε₁ : ℝ) / ε₂))
  (nn : ∀(l : List T), ∀(u : U), nq l u ≠ 0)
  (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (Habs : AbsCts (nq l₁) (nq l₂)) (h2 : Neighbour l₁ l₂) :
  (∑' (x : V),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α *
        (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤
  (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by

  -- Turn everything into an explicit PMF
  let nq_PMF (l : List T) : PMF U := ⟨ nq l, HNorm l ⟩
  have nq_PMF_coe (l : List T) (u : U) : nq l u = nq_PMF l u := by
    rw [DFunLike.coe]
    simp [PMF.instFunLike]
  conv =>
    congr
    · arg 1
      intro x
      congr
      · arg 1
        arg 1
        intro i
        rw [nq_PMF_coe]
      · arg 1
        arg 1
        intro a
        rw [nq_PMF_coe]
    · arg 1
      intro x
      rw [nq_PMF_coe]

  -- Derive the assumptions from the old proof
  have nq_nts : ∀ l : List T, ∑' n : U, nq_PMF l n ≠ ⊤ := by
    intro l
    exact PMF.tsum_coe_ne_top (nq_PMF l)

  have nq_nt : ∀ l : List T, ∀ u : U, nq_PMF l u ≠ ⊤ := by
    exact fun l u => PMF.apply_ne_top (nq_PMF l) u

  -- TODO (if needed): Renyi divergence is not Top

  -- Rewrite as cascading expectations
  simp [zCDPBound, RenyiDivergence] at h
  rw [RenyiDivergenceExpectation]
  case h => apply h1
  case H => sorry
  simp
  rw [RenyiDivergenceExpectation (fun x => DFunLike.coe (nq_PMF l₁) x) (fun x => nq l₂ x) h1 Habs]
  conv =>
    rhs
    arg 1
    intro x
    rw [nq_PMF_coe]

  -- Shuffle the sum
  rw [fiberwisation (fun x => (nq_PMF l₁ x / nq_PMF l₂ x) ^ α * nq_PMF l₂ x) f]
  apply ENNReal.tsum_le_tsum
  intro i
  simp

  -- Eliminate epements with probability zero
  split
  case h.inl =>
    rename_i H
    repeat rw [condition_to_subset]
    rw [H]
    simp

  -- Part 2: Apply Jensen's inequality to the normalized fibers
  rename_i NotEmpty
  repeat rw [condition_to_subset]

  have MasterRW : ∀ l : List T, ∑' (a : ↑{a | i = f a}), nq_PMF l ↑a ≠ ⊤ := by
    intro l
    exact convergent_subset (fun y => f y) (nq_nts l)

  have MasterZero : ∀ l : List T, ∑' (a : ↑{a | i = f a}), nq_PMF l ↑a ≠ 0 := by
    intro l
    simp
    have T := witness NotEmpty
    cases T
    rename_i z w
    exists z
    constructor
    . trivial
    . apply nn l
  simp

  have Hac : AbsCts (δpmf (nq_PMF l₁) f i (MasterZero l₁) (MasterRW l₁)) (δpmf (nq_PMF l₂) f i (MasterZero l₂) (MasterRW l₂)) := by sorry
  rw [AbsCts] at Hac

  have HJ := Renyi_Jensen_ENNReal (δpmf (nq_PMF l₁) f i (MasterZero l₁) (MasterRW l₁)) (δpmf (nq_PMF l₂) f i (MasterZero l₂) (MasterRW l₂)) h1 Hac

  have δnt (x : { x // i = f x }) (l : List T) : (δpmf (nq_PMF l) f i (MasterZero l) (MasterRW l) x) ≠ ⊤ := by sorry

  have Hspecial (x : { x // i = f x }) : ¬((δpmf (nq_PMF l₁) f i (MasterZero l₁) (MasterRW l₁) x) ≠ 0 ∧ (δpmf (nq_PMF l₂) f i (MasterZero l₂) (MasterRW l₂) x) = ⊤) := by
    simp
    intro _ Hcont
    exfalso
    apply δnt
    apply Hcont

  -- Cancel the δPMF on the LHS of HJ, its sum is 1
  conv at HJ =>
    lhs
    arg 1
    arg 1
    intro x
    rw [division_def]
    rw [mul_mul_inv_eq_mul_cancel (Hac x) (Hspecial x)]
  conv at HJ =>
    lhs
    arg 1
    rw [PMF.tsum_coe]
  simp at HJ

  -- Unfold normalization constants from δpmf
  let N (l : List T) := (∑' (x : {n // i = f n}), nq_PMF l x)⁻¹
  have N_def (l : List T) : N l =  (∑' (x : {n // i = f n}), nq_PMF l x)⁻¹ := by sorry -- exact rfl
  have N_inv (l : List T) : (∑' (x : {n // i = f n}), nq_PMF l x) = (N l)⁻¹ := by sorry -- exact rfl
  have δpmf_N (l : List T) (x : { x // i = f x }) : (δpmf (nq_PMF l) f i (MasterZero l) (MasterRW l)) x = (N l) * nq_PMF l x := by
    simp [δpmf]
    unfold δ
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
    rw [N_def]
    rw [mul_comm]
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
  conv at HJ =>
    rhs
    arg 1
    intro x
    simp [δpmf]
    unfold δ
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
    rw [<- N_def]
    rw [<- N_def]

  -- Simplify constants in goal
  rw [N_inv]
  rw [N_inv]

  -- Simplify constants in HJ
  have C (x : { n // i = f n }) : (((nq_PMF l₁) ↑x * N l₁ / ((nq_PMF l₂) ↑x * N l₂)) : ENNReal) =  ((N l₁ / N l₂) * ((nq_PMF l₁) ↑x / ((nq_PMF l₂) ↑x )) : ENNReal) := by sorry
  conv at HJ =>
    rhs
    arg 1
    intro x
    arg 1
    arg 1
    rw [C]
  clear C

  have Hα' : 0 <= α := by
    linarith

  conv at HJ =>
    rhs
    arg 1
    intro x
    arg 1
    rw [ENNReal.mul_rpow_of_nonneg _ _ Hα']
  conv at HJ =>
    rhs
    arg 1
    intro x
    rw [mul_assoc]
    arg 2
    rw [<- mul_assoc]
    rw [mul_comm]
  rw [ENNReal.tsum_mul_left] at HJ
  rw [ENNReal.tsum_mul_left] at HJ

  -- Apply transitivity with HJ
  rw [<- mul_assoc] at HJ
  rw [mul_comm] at HJ
  apply (ENNReal.div_le_iff_le_mul ?G1 ?G2).mpr at HJ
  apply (le_trans ?G3 HJ)

  -- These are equal
  sorry




theorem tsum_ne_zero_of_ne_zero {T : Type} [Inhabited T] (f : T → ENNReal) (h : ∀ x : T, f x ≠ 0) :
  ∑' x : T, f x ≠ 0 := by
  by_contra CONTRA
  rw [ENNReal.tsum_eq_zero] at CONTRA
  have A := h default
  have B := CONTRA default
  contradiction



theorem DPostPocess_pre_reduct_1 {nq : List T → SLang U} {HNorm : ∀ l, HasSum (nq l) 1} {ε₁ ε₂ : ℕ+}
  (h : zCDPBound nq HNorm ((ε₁ : ℝ) / ε₂)) (nn : ∀(l : List T), ∀(u : U), nq l u ≠ 0)
  (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (Habs : AbsCts (nq l₁) (nq l₂)) (h2 : Neighbour l₁ l₂) :
  (∑' (x : V),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α *
        (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤
  (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by

  -- Next I need to generalize the fiberwisation argument to eliminate the side conditions and work in
  -- the extended reals
  -- I'll also have to generalize the δpmf normalization, though that should mstly just be making sure the correct terms are PMFs
  -- That should bring be down to the extended Renyi divergence

  -- This lemma should be provable as stated
  sorry



theorem DPostPocess_pre {nq : List T → SLang U} {HNorm : ∀ l, HasSum (nq l) 1} {ε₁ ε₂ : ℕ+}
  (h : zCDPBound nq HNorm ((ε₁ : ℝ) / ε₂))
  (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (Habs : AbsCts (nq l₁) (nq l₂)) (h2 : Neighbour l₁ l₂) :
  (∑' (x : V),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α *
        (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤
  (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by
  -- First step is to reduce to the case where (nq l) is nonzero (reduct_1)


  -- have K1 : Function.support (fun (a : U) => if x = f a then nq l₁ a else 0) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]

  -- have K2 : Function.support (fun x : T => (p x / q x)^α * q x) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]
  -- rw [<- tsum_subtype_eq_of_support_subset K1] at Hsumeq
  -- rw [<- tsum_subtype_eq_of_support_subset K2] at Hsumeq
  -- simp at Hsumeq

  sorry



theorem privPostProcess_zCDPBound {nq : List T → SLang U} {HNorm : NormalMechanism nq} {ε₁ ε₂ : ℕ+}
  (h : zCDPBound nq HNorm ((ε₁ : ℝ) / ε₂)) (f : U → V) (Hac : ACNeighbour nq) :
  zCDPBound (privPostProcess nq f) (privPostProcess_norm nq HNorm f) ((ε₁ : ℝ) / ε₂) := by
  simp [privPostProcess, zCDPBound, RenyiDivergence]
  intro α h1 l₁ l₂ h2
  have h' := h
  simp [zCDPBound, RenyiDivergence] at h'
  replace h' := h' α h1 l₁ l₂ h2
  apply le_trans _ h'
  clear h'
  unfold RenyiDivergence_def
  rw [DFunLike.coe]
  rw [PMF.instFunLike]
  simp
  conv =>
    lhs
    arg 1
    arg 2
    arg 1
    arg 1
    intro x
    repeat rw [SLang.toPMF]
    simp
  conv =>
    rhs
    arg 1
    arg 2
    arg 1
    arg 1
    intro x
    repeat rw [SLang.toPMF]
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
  apply ofEReal_le_mono
  apply ereal_smul_left_le
  · apply EReal.coe_pos.mpr
    apply inv_pos_of_pos
    linarith
  · exact EReal.coe_lt_top (α - 1)⁻¹
  apply elog_mono_le.mp
  apply (DPostPocess_pre h f h1 ?Gabs h2)
  case Gabs => exact Hac l₁ l₂ h2



  /-
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
  sorry
  -/

-- theorem privPostProcess_NonTopRDNQ {nq : List T → SLang U} {HNorm : ∀ l, HasSum (nq l) 1} {ε₁ ε₂ : ℕ+} (f : U → V)
--   (dp : zCDPBound nq HNorm ((ε₁ : ℝ) / ε₂)) (nt : NonTopRDNQ nq) (nz : NonZeroNQ nq) (nts : NonTopNQ nq) (ntsum: NonTopSum nq) :
--   NonTopRDNQ (privPostProcess nq f) := by
--   simp [NonTopRDNQ, NonTopSum, privPostProcess] at *
--   intros α h1 l₁ l₂ h2
--   have ntrdnq := nt
--   replace nt := nt α h1 l₁ l₂ h2
--   sorry
--   -- have A := @DPostPocess_pre T U V _ _ _ nq ε₁ ε₂ dp nz ntrdnq nts ntsum f α h1 l₁ l₂ h2
--   -- apply @LT.lt.ne_top _ _ _ _ ⊤
--   -- rw [Eq.comm] at nt
--   -- have B := Ne.lt_top' nt
--   -- exact lt_of_le_of_lt A B




def privPostProcess_AC {f : U -> V} (nq : List T → SLang U) (Hac : ACNeighbour nq) : ACNeighbour (privPostProcess nq f) := by
  rw [ACNeighbour] at *
  unfold AbsCts at *
  intro l₁ l₂ Hn v
  have Hac := Hac l₁ l₂ Hn
  simp [privPostProcess]
  intro Hppz i fi
  apply Hac
  apply Hppz
  apply fi

/--
Postprocessing preserves zCDP
-/
theorem privPostProcess_zCDP {f : U → V}
  (nq : List T → SLang U) (ε₁ ε₂ : ℕ+) (h : zCDP nq ((ε₁ : ℝ) / ε₂)) :
  zCDP (privPostProcess nq f) (((ε₁ : ℝ) / ε₂)) := by
  rcases h with ⟨ Hac1, ⟨ Hn1, Hb1 ⟩⟩
  simp [zCDP] at *
  apply And.intro
  · exact privPostProcess_AC nq Hac1
  · exists (privPostProcess_norm nq Hn1 f)
    exact (privPostProcess_zCDPBound Hb1 f Hac1)

end SLang
