/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang

/-! # Implementation for geometric distribution over natural numbers -/

noncomputable section

namespace SLang

section Geometric

variable (trial : SLang Bool)

-- MARKUSDE: remove?
-- variable (trial_spec : trial false + trial true = 1)
-- variable (trial_spec' : trial true < 1)


/-- Termination condition: Body has sampled ``true``. -/
def loop_cond (st : Bool × ℕ) : Bool := st.1

/-- Sampling program: sample from ``trial`` and increment the number of attempts. -/
def loop_body (st : Bool × ℕ) : SLang (Bool × ℕ):= do
  let x ← trial
  return (x,st.2 + 1)

/-- ``SLang`` term for a geometric distrubution on ``Nat``. Iteratively samples
  from ``trial``, returning the number of attempts before a ``true`` sample. -/
-- MARKUSDE: FIXME-- probably violates the eventual naming scheme
def geometric : SLang ℕ := do
  let st ← probWhile loop_cond (loop_body trial) (true,0)
  return st.2

end Geometric

end SLang
