import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import KolmogorovExtension4.KolmogorovExtension
import KolmogorovExtension4.IndependentFamily
import Mathlib.Topology.EMetricSpace.Basic

import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory MeasurableSpace Measure Pmf TopologicalSpace BorelSpace

#check Measure.subset_pi

theorem Foo : ((1: ENNReal) / 2) ≤ 1 := sorry

@[simp]
noncomputable def Flip : Pmf Bool := bernoulli (1/2) Foo

theorem test1 : Flip true = 1 / 2 := by
  simp

@[simp]
noncomputable def Coin : Measure Bool := Flip.toMeasure

theorem test2 : Coin { b | b = true } = 1 / 2 := by
  simp



-- noncomputable abbrev Family (_ : ℕ) := Coin
instance H : MeasurableSpace (∀ _ : ℕ, Bool) := ⊤

abbrev BitStream (i : ℕ) : Type := Bool

-- def projection (i : ℕ) : Bool := BitStream i

variable {ι : ℕ → Bool} [O : MeasurableSpace (∀ _ : ℕ, Bool)]


def μ : Measure (ℕ → Bool) := sorry

def proj (μ : Measure (ℕ → Bool)) (i : ℕ) : Measure Bool := sorry

theorem μ_prop1 : forall i : ℕ, proj μ i = Coin := sorry



noncomputable def P (i : ℕ) : Measure (BitStream i) := Flip.toMeasure

instance inst1 (i : ℕ) : MeasurableSpace (BitStream i) := ⊤
--instance inst2 (i : ℕ) : PseudoEMetricSpace (BitStream i) := sorry
--instance instx1 (i : ℕ) : TopologicalSpace (BitStream i) := (@UniformSpace.toTopologicalSpace (BitStream i) (@PseudoEMetricSpace.toUniformSpace (BitStream i) (inst2 i)))
--instance inst3 (i : ℕ) : BorelSpace (BitStream i) := sorry
--instance instx2 (i : ℕ) : UniformSpace (BitStream i) := (@PseudoEMetricSpace.toUniformSpace (BitStream i) (inst2 i))
--instance inst5 (i : ℕ) : CompleteSpace (BitStream i) := @CompleteSpace (BitStream i) (instx2 i)
--instance inst6 (i : ℕ) : Nonempty (BitStream i) := sorry
instance inst7 (i : ℕ) : IsProbabilityMeasure (P i) := toMeasure.isProbabilityMeasure Flip

--set_option pp.all true

-- noncomputable def μ : Measure (ℕ → Bool) := @independentFamily ℕ BitStream inst1 inst2 inst3 inst4 inst5 inst6 P inst7

instance : MeasurableSpace ℝ := ⊤
instance : MetricSpace ℝ := ⊤
instance : PseudoEMetricSpace ℝ := ⊤
instance : EMetricSpace ℝ := ⊤
instance : TopologicalSpace ℝ := ⊤
instance : BorelSpace ℝ := ⊤
instance : UniformSpace ℝ := ⊤
instance : CompleteSpace ℝ := ⊤
instance : Nonempty ℝ := ⊤
