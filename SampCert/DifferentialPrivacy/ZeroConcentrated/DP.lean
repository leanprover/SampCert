/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.ConcentratedBound
import SampCert.SLang
import SampCert.Samplers.GaussianGen.Basic
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# Zero Concentrated Differential Privacy

This file defines zero concentrated differential privacy (zCDP).
-/


/--
Definition of zCDP in terms of Renyi Divergence between neighbouring databases.
-/
def DP (q : List T → SLang U) (ε : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence (q l₁) (q l₂) α ≤ (1/2) * ε ^ 2 * α

/--
No element in the output of a mechanism occurs with zero probability.
-/
def NonZeroNQ (nq : List T → SLang U) : Prop :=
  ∀ l : List T, ∀ n : U, nq l n ≠ 0

/--
The output distribution of a mechanism has a finite sum.
-/
def NonTopSum (nq : List T → SLang U) : Prop :=
  ∀ l : List T, ∑' n : U, nq l n ≠ ⊤

/--
Each value in the output distribution of a mechanism is finite.
-/
def NonTopNQ (nq : List T → SLang U) : Prop :=
  ∀ l : List T, ∀ n : U, nq l n ≠ ⊤

/--
The Renyi divergence between neighbouring elements of the output of ``nq`` is finite.
-/
def NonTopRDNQ (nq : List T → SLang U) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  ∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α) ≠ ⊤

-- def NonZeroRDNQ (nq : List T → SLang U) : Prop :=
--   ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
--   ∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α) ≠ 0


/--
Zero-concentrated differential privacy
-/
def zCDP (q : List T → SLang U) (ε : ℝ) : Prop :=
    DP q ε
  ∧ NonZeroNQ q
  ∧ NonTopSum q
  ∧ NonTopNQ q
  ∧ NonTopRDNQ q
  -- ∧ NonZeroRDNQ q
