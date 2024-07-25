/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang
import Mathlib.Data.ByteArray

open SLang Std Int Array PMF



-- MARKUSDE: Remove this file, and the Scratch build target, before merging
def main : IO Unit := do
  IO.println "Goodbye SampCert"
  -- let _ ← run <| (DiscreteGaussianPMF 1 2 2)
  let x <- run <| (⟨SLang.UniformByte, sorry⟩ : PMF UInt8)
  IO.println "Hello SampCert"
  IO.println x

--   toSLang ⟨ fun _ => ,
--             by
--               rw [Summable.hasSum_iff ENNReal.summable]
--               rw [division_def]
--               rw [ENNReal.tsum_mul_right]
--               rw [tsum_eq_finsum]
--               · sorry
--               · sorry
--             ⟩
