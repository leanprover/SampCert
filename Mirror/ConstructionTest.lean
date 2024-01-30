import KolmogorovExtension4.independentFamily

open scoped NNReal

open MeasureTheory

section test

variable {ι : Type*} [Nonempty ι]
  {α : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ i, Nonempty (α i)] [∀ i, BorelSpace (α i)]
  (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]

noncomputable
def independentFamily'  :
    Measure (∀ i, α i) :=
  projectiveLimit (Measure.subset_pi P) (product_isProjective P)

instance (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    IsProbabilityMeasure (independentFamily' P) := by
  rw [independentFamily']
  infer_instance

end test

noncomputable
def Bernoulli_half : Measure ℝ :=
  ((1 : ℝ≥0) / 2) • Measure.dirac 0 + ((1 : ℝ≥0) / 2) • Measure.dirac 1

instance : IsProbabilityMeasure Bernoulli_half := by
  constructor
  simp only [Bernoulli_half, Measure.add_toOuterMeasure, Measure.smul_toOuterMeasure,
    OuterMeasure.coe_add, OuterMeasure.coe_smul, Pi.add_apply, Pi.smul_apply, MeasurableSet.univ,
    Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem, Pi.one_apply]
  simp only [ENNReal.smul_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    ENNReal.coe_div, ENNReal.coe_ofNat, smul_eq_mul, mul_one]
  rw [ENNReal.add_halves]
  simp only [ENNReal.coe_one]

noncomputable
def NBernoulli_half : Measure (ℕ → ℝ) := independentFamily' (fun _ ↦ Bernoulli_half)

instance H : IsProbabilityMeasure NBernoulli_half := by
  rw [NBernoulli_half]
  infer_instance
