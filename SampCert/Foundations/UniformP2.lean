/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Random
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Nat.Log

open PMF Nat

-- Assumption: the Dafny version indeed has this spec

noncomputable def UniformPowerOfTwoSample (n : PNat) : RandomM Nat :=
  uniformOfFintype (Fin (2 ^ (log 2 n)))

@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := sorry
