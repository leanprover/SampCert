/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang

-- Entry point to check properties of the FFI

def sample_byte : IO UInt8 := PMF.run <|
  (⟨SLang.UniformByte,
    by sorry ⟩ : PMF UInt8)

def main : IO Unit := do
  -- Check if FFI is working
  IO.print "Sampling byte: "
  let x <- sample_byte
  IO.println x
