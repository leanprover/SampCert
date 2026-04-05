/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Code
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Properties

namespace SLang

variable (T : ℤ) (ε₁ ε₂ : ℕ+) {sv_T : Type}
variable (qs : sv_query sv_T)
variable (HL : has_lucky qs T)

def snoc {T : Type*} (x : T) (L : List T) := L ++ [x]

-- "Sparse" algorithm as described in the proof of 3.25 of
-- Cynthia Dwork and Aaron Roth "The Algorithmic Foundations of Differential Privacy" (2014)

def shift_qs (n : ℕ) (qs : sv_query sv_T) : sv_query sv_T := fun i => qs (i + n)

lemma shift_qs_lucky n (qs' : sv_query sv_T) (H : has_lucky qs' T) : has_lucky (shift_qs n qs') T := by
  intro τ l
  rcases (H τ l) with ⟨ K, HK ⟩
  exists K
  intro A K' HK'
  simp only [shift_qs]
  apply HK
  trivial

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

def privSparseAux {sv_T : Type} (qs' : sv_query sv_T) (HL' : has_lucky qs' T) (c : ℕ) : Mechanism sv_T (List ℕ) :=
  match c with
  | 0 => privConst []
  | Nat.succ c' =>
      privPostProcess
        (privComposeAdaptive
          (sv1_aboveThresh_PMF qs' T HL' ε₁ ε₂)
          (fun n => privSparseAux (shift_qs n qs') (shift_qs_lucky T n qs' HL') c'))
      (Function.uncurry snoc)

def privSparse (c : ℕ) : Mechanism sv_T (List ℕ) :=
  privSparseAux T ε₁ ε₂ (shift_qs 0 qs) (shift_qs_lucky _ _ _ HL) c

end SLang
