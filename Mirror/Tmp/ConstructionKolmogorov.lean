import KolmogorovExtension4.KolmogorovExtension

open MeasureTheory Measure Topology BorelSpace

abbrev BitStream (n : ℕ) : Type := ℝ

instance inst1 (i : ℕ) : MeasurableSpace (BitStream i) := ⊤
instance inst2 (i : ℕ) : Nonempty (BitStream i) := sorry
instance inst3 (i : ℕ) : TopologicalSpace (BitStream i) := ⊤
instance inst4 (i : ℕ) : BorelSpace (BitStream i) := sorry
instance inst5 (i : ℕ) : PolishSpace (BitStream i) := sorry

theorem P : ∀ J : Finset ℕ, Measure (∀ j : J, BitStream j) := sorry

instance inst6 (i : Finset ℕ) : IsFiniteMeasure (P i) := sorry

theorem I : IsProjectiveMeasureFamily P := sorry

#check @projectiveLimit Nat BitStream inst1 inst2 inst3 inst4 inst5 P inst6 I

noncomputable def μ : Measure (ℕ → ℝ) := @projectiveLimit Nat BitStream inst1 inst2 inst3 inst4 inst5 P inst6 I
