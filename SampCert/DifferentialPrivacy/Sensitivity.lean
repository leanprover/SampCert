/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.SLang
import SampCert.DifferentialPrivacy.Neighbours

/-!
# Sensitivity

Notion of the "sensitivity" of a query over lists.
-/

open Classical Nat Int Real

variable {T : Type}

/--
A query `q` has sensivity `Δ`.

Namely, `|q(x) - q(x')| ≤ Δ` for neighbouring lists `x` and `x'`.
-/
noncomputable def sensitivity (q : List T → ℤ) (Δ : ℕ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → Int.natAbs (q l₁ - q l₂) ≤ Δ
