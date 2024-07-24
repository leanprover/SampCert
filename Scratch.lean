/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang

open SLang Std Int Array PMF


-- MARKUSDE: Remove this file, and the Scratch build target, before merging

def main : IO Unit := do
  let x : Array UInt8 <- run <| SLang.UniformByteArray 5
  IO.print "Hello SampCert"
