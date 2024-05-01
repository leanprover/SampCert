/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
--import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open Real ENNReal

variable {T : Type}

noncomputable def RenyiDivergence (p q : T → ℝ) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (∑' x : T, (p x)^α  * (q x)^(1 - α))
