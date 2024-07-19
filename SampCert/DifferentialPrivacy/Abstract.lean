/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.Foundations.Basic

/-!
# Differential Privacy

This file defines an abstract system of differentially private operators.
-/

noncomputable section

open Classical Nat Int Real ENNReal

namespace SLang

/--
Abstract definition of a differentially private systemm.
-/
class DPSystem (T : Type) where
  /--
  Differential privacy proposition, with one real paramater (ε-DP, ε-zCDP, etc)
  -/
  prop : Mechanism T Z → NNReal → Prop
  /--
  DP is monotonic
  -/
  prop_mono {m : Mechanism T Z} {ε₁ ε₂: NNReal} (Hε : ε₁ ≤ ε₂) (H : prop m ε₁) : prop m ε₂
  /--
  A noise mechanism (eg. Laplace, Discrete Gaussian, etc)
  Paramaterized by a query, sensitivity, and a (rational) security paramater.
  -/
  noise : Query T ℤ → (sensitivity : ℕ+) → (num : ℕ+) → (den : ℕ+) → Mechanism T ℤ
  /--
  Adding noise to a query makes it private.
  -/
  noise_prop : ∀ q : List T → ℤ, ∀ Δ εn εd : ℕ+, sensitivity q Δ → prop (noise q Δ εn εd) (εn / εd)
  /--
  Privacy composes by addition.
  -/
  compose_prop : {U V : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → [MeasurableSpace V] → [Countable V] → [DiscreteMeasurableSpace V] → [Inhabited V] →
    ∀ m₁ : Mechanism T U, ∀ m₂ : Mechanism T V, ∀ ε₁ ε₂ : NNReal,
    prop m₁ ε₁ → prop m₂ ε₂ → prop (privCompose m₁ m₂) (ε₁ + ε₂)
  /--
  Privacy adaptively composes by addition.
  -/
  adaptive_compose_prop : {U V : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → [MeasurableSpace V] → [Countable V] → [DiscreteMeasurableSpace V] → [Inhabited V] → ∀ m₁ : Mechanism T U, ∀ m₂ : U -> Mechanism T V,
    ∀ ε₁ ε₂ : NNReal,
    prop m₁ ε₁ → (∀ u, prop (m₂ u) ε₂) -> prop (privComposeAdaptive m₁ m₂) (ε₁ + ε₂)
  /--
  Privacy is invariant under post-processing.
  -/
  postprocess_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → { pp : U → V } →
    ∀ m : Mechanism T U, ∀ ε : NNReal,
   prop m ε → prop (privPostProcess m pp) ε
  /--
  Constant query is 0-DP
  -/
  const_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] -> (u : U) -> prop (privConst u) (0 : NNReal)


lemma DPSystem_prop_ext [dps : DPSystem T] {ε₁ ε₂ : NNReal} (m : Mechanism T U) (Hε : ε₁ = ε₂) (H : dps.prop m ε₁) :
    dps.prop m ε₂ := by
  rw [<- Hε]
  assumption


@[simp]
lemma bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → PMF A) :
    (fun l => (p l) >>= (fun a : U => (q l) >>= fun b : V => h a b)) =
    fun l => (privCompose p q l) >>= (fun z => h z.1 z.2) := by
  ext l x
  simp [privCompose, tsum_prod']

lemma compose_sum_rw (nq1 : U -> ENNReal) (nq2 : V -> ENNReal) (b : U) (c : V) :
  (∑' (a : U), nq1 a * ∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = nq1 b * nq2 c := by
  have A : ∀ a : U, ∀ b : U, (∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = if b = a then (∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0) else 0 := by
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
  have B : ∀ x : U, (if x = b then 0 else if b = x then nq1 x * ∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0 else 0) = 0 := by
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
  have C :∀ x : V,  (if x = c then 0 else if c = x then nq2 x else 0) = 0 := by
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


/--
Partition series into fibers. `g` maps an element to its fiber.
-/
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

/--
Partition series into fibers. `g` maps an element to its fiber.
-/
theorem ENNReal.tsum_fiberwise (p : T → ENNReal) (f : T → V) :
  ∑' (x : V), ∑' (b : (f ⁻¹' {x})), p b
    = ∑' i : T, p i := by
  apply HasSum.tsum_eq
  apply ENNReal.HasSum_fiberwise
  apply Summable.hasSum
  exact ENNReal.summable

/--
Rewrite a series into a sum over fibers. `f` maps an element into its fiber.
-/
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

lemma condition_to_subset (f : U → V) (g : U → ENNReal) (x : V) :
  (∑' a : U, if x = f a then g a else 0) = ∑' a : { a | x = f a }, g a := by
  have A := @tsum_split_ite U (fun a : U => x = f a) g (fun _ => 0)
  simp only [decide_eq_true_eq, tsum_zero, add_zero] at A
  rw [A]
  have B : ↑{i | decide (x = f i) = true} = ↑{a | x = f a} := by
    simp
  rw [B]

end SLang
