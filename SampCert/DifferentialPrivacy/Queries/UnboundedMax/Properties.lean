/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Abstract

noncomputable section
open Classical

namespace SLang

/-
## Helper programs
-/

/--
Sum over a list, clipping each element to a maximum.

Similar to exactBoundedSum, however exactClippedSum allows m = 0.
-/
def exactClippedSum (m : ℕ) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n m)) l)

/--
Rate at which a given clipping thresold is impacting the accuracy of the sum.

Always negative or zero.
-/
def exactDiffSum (m : ℕ) (l : List ℕ) : ℤ := exactClippedSum m l - exactClippedSum (m + 1) l

/--
Noise the constant 0 value using the abstract noise function.

This looks strange, but will specialize to Lap(ε₁/ε₂, 0) in the pure DP case.
-/
def privNoiseZero [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) : SLang ℤ := dps.noise (fun _ => 0) 1 ε₁ ε₂ []

/--
Not used for anything, but to give confidence in our definitions

(exactDiffSum l m) is zero if and only if m is an upper bound on the list elements
-/
lemma exactDiffSum_eq_0_iff_ge_max (l : List ℕ) (m : ℕ) :
    l.maximum ≤ m <-> exactDiffSum m l = 0 := by
  apply Iff.intro
  · induction l
    · simp [exactDiffSum, exactClippedSum]
    · rename_i l0 ls IH
      intro Hmax
      simp [List.maximum_cons] at Hmax
      rcases Hmax with ⟨ Hmax0, Hmax1 ⟩
      have IH' := IH Hmax1
      clear IH
      simp [exactDiffSum, exactClippedSum] at *
      rw [add_sub_add_comm]
      rw [IH']
      rw [Int.min_def, Int.min_def]
      split
      · split
        · simp
        · linarith
      · exfalso
        rename_i h
        apply h
        simp
        rw [Nat.cast_withBot, WithBot.coe_le_coe] at Hmax0
        trivial
  · intro H1
    apply List.maximum_le_of_forall_le
    revert H1
    induction l
    · simp
    · rename_i l0 ls IH
      intro Hdiff a Ha
      rw [List.mem_cons_eq] at Ha
      cases Ha
      · sorry
      · apply IH
        · sorry
        · trivial



/-
## Program version 0
  - Executable
  - Tracks single state
-/
