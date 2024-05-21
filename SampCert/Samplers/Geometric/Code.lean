/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang

noncomputable section

namespace SLang

section Geometric

variable (trial : SLang Bool)
variable (trial_spec : trial false + trial true = 1)
variable (trial_spec' : trial true < 1)

def loop_cond (st : (Bool × ℕ)) : Bool := st.1
def loop_body (st : (Bool × ℕ)) : SLang (Bool × ℕ) := do
  let x ← trial
  return (x,st.2 + 1)

def geometric : SLang ℕ := do
  let st ← probWhile loop_cond (loop_body trial) (true,0)
  return st.2

end Geometric

end SLang
