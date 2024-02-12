/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Order.CompletePartialOrder

noncomputable section

open Classical ENNReal PMF

def SubPMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // ∃ x : ℝ≥0∞, x ≤ 1 ∧ HasSum f x }

namespace SubPMF

variable {α}

instance instFunLike : FunLike (SubPMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[ext]
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

instance : CompletePartialOrder (SubPMF α) := sorry

def toPMF (p : SubPMF α) (h : HasSum p 1) : PMF α := ⟨ p , h ⟩

end SubPMF

namespace PMF

def toSubPMF (p : PMF α) : SubPMF α := ⟨ p , ⟨ 1, And.intro (le_refl 1) p.2 ⟩ ⟩

end PMF

namespace SubPMF

def bind (p : SubPMF α) (f : α → SubPMF β) : SubPMF β :=
  ⟨fun b => ∑' a, p a * f a b, sorry ⟩

instance : Monad SubPMF where
  pure a := (PMF.pure a).toSubPMF
  bind pa pb := pa.bind pb

variable (p : SubPMF α) (f : α → SubPMF β) (g : β → SubPMF γ)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl



end SubPMF
