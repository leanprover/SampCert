/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Order.OmegaCompletePartialOrder

noncomputable section

open Classical NNReal ENNReal PMF

def SubPMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // ∃ x : ℝ≥0∞, x ≤ 1 ∧ HasSum f x }

namespace SubPMF

variable {α β γ : Type*}

instance instFunLike : FunLike (SubPMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[ext]
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

theorem ext_iff {p q : PMF α} : p = q ↔ ∀ x, p x = q x :=
  DFunLike.ext_iff

instance : OmegaCompletePartialOrder (SubPMF α) := sorry

def toPMF (p : SubPMF α) (h : HasSum p 1) : PMF α := ⟨ p , h ⟩

def zero : SubPMF α :=
  ⟨λ _ : α => 0 , ⟨0, And.intro (zero_le 1) (hasSum_zero)⟩⟩

@[simp]
theorem zero_apply (x : α) : zero x = 0 := sorry

end SubPMF

namespace PMF

def toSubPMF (p : PMF α) : SubPMF α := ⟨p , ⟨ 1, And.intro (le_refl 1) p.2 ⟩⟩

@[simp]
theorem toSubPMF_apply (p : PMF α) (x : α) : (toSubPMF p x) = p x := sorry

instance : Coe (PMF α) (SubPMF α) where
  coe a := toSubPMF a

end PMF

namespace SubPMF

def pure (a : α) : SubPMF α :=
  ⟨fun a' => if a' = a then 1 else 0, sorry⟩

def bind (p : SubPMF α) (f : α → SubPMF β) : SubPMF β :=
  ⟨fun b => ∑' a, p a * f a b, sorry⟩

instance : Monad SubPMF where
  pure a := pure a
  bind pa pb := pa.bind pb

variable (a a' : α)

@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

variable (p : SubPMF α) (f : α → SubPMF β) (g : β → SubPMF γ)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl

@[simp]
theorem pure_bind (a : α) (f : α → SubPMF β) : (pure a).bind f = f a := sorry

@[simp]
theorem bind_pure : p.bind pure = p := sorry

@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g := sorry

end SubPMF
