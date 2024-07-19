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

end SLang
