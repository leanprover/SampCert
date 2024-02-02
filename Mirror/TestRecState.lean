import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Pmf Finset ENNReal

#check MeasureTheory.Measure.bind_apply
#check MeasureTheory.Measure.lintegral_bind

noncomputable def zpf : ENNReal := 1 / 2

theorem base : zpf ≤ 1 := sorry

@[simp]
noncomputable def coin1 : Pmf (Fin 2):= binomial zpf base 1

@[simp]
theorem coin1Prop : coin1 0 = zpf := by
  unfold coin1
  rw [binomial_apply]
  simp
  sorry

@[simp]
noncomputable def coin2 : Pmf Bool := map (λ n : Fin 2 => if n = 0 then false else true) coin1

#check tsum
#check prod_ite_of_true

theorem coin2Prop : coin2 false = zpf := by
  unfold coin2
  rw [map_apply, tsum_fintype]
  simp only [coin1, Fin.sum_univ_two, binomial_apply_zero, ge_iff_le, pow_one, ite_true, ite_false, add_zero]
  sorry

@[simp]
noncomputable def coin3 : Pmf Bool :=
  Pmf.bind (binomial zpf base 1) (Pmf.pure ∘ (fun flip => if flip.val = 0 then false else true))

theorem coin3Prop : coin3 true = zpf := by
  unfold coin3
  rw [bind_apply]
  simp
  rw [tsum_fintype]
  conv =>
    left
    right
    intro b
    rw [binomial_apply zpf base 1 b]
    simp
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, ge_iff_le, tsub_zero, pow_one, one_mul, Nat.choose_succ_self_right, zero_add,
    Nat.cast_one, mul_one, ite_false, mul_zero, Fin.val_one, le_refl, tsub_eq_zero_of_le, Nat.choose_self, ite_true]

--set_option pp.notation false
--set_option pp.coercions false
--set_option pp.funBinderTypes true
--set_option pp.fullNames true

@[simp]
noncomputable def coin4 : Pmf Bool := do
  let flip ← binomial zpf base 1
  return if flip.val = 0 then false else true

attribute [simp] instMonadPmf

theorem coin4Prop : coin4 true = zpf := by
  unfold coin4
  simp
  rw [tsum_fintype]
  conv =>
    left
    right
    intro b
    rw [binomial_apply zpf base 1 b]
    simp
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, ge_iff_le, tsub_zero, pow_one, one_mul, Nat.choose_succ_self_right, zero_add,
    Nat.cast_one, mul_one, ite_false, mul_zero, Fin.val_one, le_refl, tsub_eq_zero_of_le, Nat.choose_self, ite_true]
