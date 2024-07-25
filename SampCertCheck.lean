/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang

-- Entry point to check properties of the FFI

def main : IO Unit := do
  -- Check if FFI is working
  IO.print "Sampling bytes: "
  for _ in [:10000] do
    let x <- PMF.run <| SLang.probUniformByte_PMF
    IO.println x
