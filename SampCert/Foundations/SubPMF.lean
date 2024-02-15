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

abbrev SubPMF.{u} (α : Type u) : Type u := α → ℝ≥0∞

namespace SubPMF

variable {α β γ : Type*}

def toPMF (p : SubPMF α) (h : HasSum p 1) : PMF α := ⟨ p , h ⟩

def zero : SubPMF α := λ _ : α => 0

@[simp]
theorem zero_apply (x : α) : zero x = 0 := by
  unfold zero
  simp

end SubPMF

namespace PMF

def toSubPMF (p : PMF α) : SubPMF α := p.1

@[simp]
theorem toSubPMF_apply (p : PMF α) (x : α) : (toSubPMF p x) = p x := by
  unfold toSubPMF
  unfold DFunLike.coe
  unfold instFunLike
  simp

instance : Coe (PMF α) (SubPMF α) where
  coe a := toSubPMF a

end PMF

namespace SubPMF

def pure (a : α) : SubPMF α := fun a' => if a' = a then 1 else 0

def bind (p : SubPMF α) (f : α → SubPMF β) : SubPMF β :=
  fun b => ∑' a, p a * f a b

instance : Monad SubPMF where
  pure a := pure a
  bind pa pb := pa.bind pb

variable (a a' : α)

@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h

variable (p : SubPMF α) (f : α → SubPMF β) (g : β → SubPMF γ)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl

@[simp]
theorem pure_bind (a : α) (f : α → SubPMF β) : (pure a).bind f = f a := by
  have : ∀ b a', ite (a' = a) (f a' b) 0 = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs with h <;> simp [h]
  ext b
  simp [this]

@[simp]
theorem bind_pure : p.bind pure = p := by
  ext x
  simp
  #check tsum_eq_single
  sorry -- doable

@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g := sorry

end SubPMF
