/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import SampCert.Extractor.Extension

namespace Lean.ToDafny

syntax (name := inline_RandomM) "inline_RandomM" : attr

initialize
  registerBuiltinAttribute {
    ref   := by exact decl_name%
    name  := `inline_RandomM
    descr := "instruct Lean to inline a RandomM computation during extraction."
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName _ _attrKind => do
     modifyEnv fun env => extension.addEntry env (.addInline declName)
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
