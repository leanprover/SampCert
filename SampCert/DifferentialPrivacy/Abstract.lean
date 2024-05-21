/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Sensitivity

abbrev Mechanism (T U : Type) := List T → SLang U

variable { T U V : Type }
variable [MeasurableSpace U]
variable [Countable U]
variable [DiscreteMeasurableSpace U]
variable [Inhabited U]
variable [MeasurableSpace V]
variable [Countable V]
variable [DiscreteMeasurableSpace V]
variable [Inhabited V]

class DPSystem where
  prop : Mechanism T Z → ℝ → Prop
  noise : (List T → ℤ) → ℕ+ → ℕ+ → ℕ+ → Mechanism T ℤ
  noise_prop : ∀ q : List T → ℤ, ∀ Δ εn εd : ℕ+, sensitivity q Δ → prop (noise q Δ εn εd) (εn / εd)
  compose : Mechanism T U → Mechanism T V → Mechanism T (U × V)
  compose_prop : ∀ m₁ : Mechanism T U, ∀ m₂ : Mechanism T V, ∀ ε₁ ε₂ ε₃ ε₄ : ℕ+,
    prop m₁ (ε₁ / ε₂) → prop m₂ (ε₃ / ε₄) → prop (compose m₁ m₂) ((ε₁ / ε₂) + (ε₃ / ε₄))
  postprocess : Mechanism T U → (U → V) → Mechanism T V
  postprocess_prop : ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+, ∀ pp : U → V,
    prop m (ε₁ / ε₂) → prop (postprocess m pp) (ε₁ / ε₂)

-- class DPSystem where
--   prop : {U : Type} → Mechanism T U → ℝ → Prop
--   noise : (List T → ℤ) → ℕ+ → ℕ+ → ℕ+ → Mechanism T ℤ
--   noise_prop : ∀ q : List T → ℤ, ∀ Δ εn εd : ℕ+, sensitivity q Δ → prop (noise q Δ εn εd) (εn / εd)
--   compose : {U V : Type} → Mechanism T U → Mechanism T V → Mechanism T (U × V)
--   compose_prop : {U V : Type} → [Inhabited U] → [Inhabited V] → ∀ m₁ : Mechanism T U, ∀ m₂ : Mechanism T V, ∀ ε₁ ε₂ ε₃ ε₄ : ℕ+,
--     prop m₁ (ε₁ / ε₂) → prop m₂ (ε₃ / ε₄) → prop (compose m₁ m₂) ((ε₁ / ε₂) + (ε₃ / ε₄))
--   postprocess : {U : Type} → Mechanism T U → (U → V) → Mechanism T V
--   postprocess_prop : {U V : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+, ∀ pp : U → V,
--     prop m (ε₁ / ε₂) → prop (postprocess m pp) (ε₁ / ε₂)
