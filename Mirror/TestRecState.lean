
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.MeasureTheory.Measure.GiryMonad

open Pmf

#check MeasureTheory.Measure.bind_apply
#check MeasureTheory.Measure.lintegral_bind

theorem base : ((1 : ENNReal) / 2) ≤ 1 := sorry

@[simp]
noncomputable def coin1 : Pmf (Fin 2):= binomial (1/2) base 1

@[simp]
theorem coin1Prop : coin1 0 = 1 / 2 := by
  unfold coin1
  rw [binomial_apply]
  simp

@[simp]
noncomputable def coin2 : Pmf Bool := map (λ n : Fin 2 => if n = 0 then false else true) coin1

#check tsum

theorem coin2Prop : coin2 true = 1 / 2 := by
  unfold coin2
  rw [map_apply]
  simp


@[simp]
noncomputable def coin3 : Pmf Bool := do
  let flip ← binomial (1/2) base 1
  return if flip.val = 0 then false else true

--set_option pp.notation false

theorem coin3Prop : coin3 true = 1 / 2 := by
  sorry
