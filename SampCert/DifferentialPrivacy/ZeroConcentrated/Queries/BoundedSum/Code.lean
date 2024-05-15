/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Mechanism.Mechanism
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order

open Classical Nat Int Real

noncomputable section

namespace SLang

def BoundedSumQuery (U : ℕ+) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n U)) l)

end SLang
