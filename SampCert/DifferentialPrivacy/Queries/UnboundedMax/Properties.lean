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

/-
Not used for anything, but to give confidence in our definitions

(exactDiffSum l m) is zero if and only if m is an upper bound on the list elements
-/
-- lemma exactDiffSum_eq_0_iff_ge_max (l : List ℕ) (m : ℕ) :
--     l.maximum ≤ m <-> exactDiffSum m l ≤ 0 := by
--   apply Iff.intro
--   · induction l
--     · simp [exactDiffSum, exactClippedSum]
--     · rename_i l0 ls IH
--       intro Hmax
--       simp [List.maximum_cons] at Hmax
--       rcases Hmax with ⟨ Hmax0, Hmax1 ⟩
--       have IH' := IH Hmax1
--       clear IH
--       simp [exactDiffSum, exactClippedSum] at *
--       apply Int.add_le_of_le_neg_add
--       apply le_trans IH'
--       simp
--   · intro H1
--     apply List.maximum_le_of_forall_le
--     revert H1
--     induction l
--     · simp
--     · rename_i l0 ls IH
--       intro Hdiff a Ha
--       rw [List.mem_cons_eq] at Ha
--       cases Ha
--       · rename_i H
--         rw [H]
--         rw [Nat.cast_withBot]
--         apply WithBot.coe_le_coe.mpr
--
--         sorry
--       · apply IH; clear IH
--         · simp only [exactDiffSum, exactClippedSum] at *
--           have H : (min (l0.cast : ℤ) (m.cast : ℤ) - min (l0.cast) ((m.cast : ℤ) + 1)) = 0 := by
--             sorry
--           -- rw [H] at Hdiff
--           -- rw [<- Hdiff]
--           -- simp
--           sorry
--         · trivial


/-
## Program version 0
  - Executable
  - Tracks single state
-/

def sv0_state : Type := ℕ × ℤ

def sv0_threshold (s : sv0_state) : ℕ := s.1

def sv0_noise (s : sv0_state) : ℤ := s.2

def sv0_privMaxC (τ : ℤ) (l : List ℕ) (s : sv0_state) : Bool :=
  decide (exactDiffSum (sv0_threshold s) l + (sv0_noise s) < τ)

def sv0_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv0_state) : SLang sv0_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  let n := (sv0_threshold s) + 1
  return (n, vn)

def sv0_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0)
  return (sv0_threshold sk)

/-
## Program version 1
  - Executable
  - Tracks history of samples
-/

def sv1_state : Type := List ℤ × ℤ

def sv1_threshold (s : sv1_state) : ℕ := List.length s.1

def sv1_noise (s : sv1_state) : ℤ := s.2

def sv1_privMaxC (τ : ℤ) (l : List ℕ) (s : sv1_state) : Bool :=
  decide (exactDiffSum (sv1_threshold s) l + (sv1_noise s) < τ)

def sv1_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv1_state) : SLang sv1_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  return (s.1 ++ [s.2], vn)

def sv1_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
  return (sv1_threshold sk)

/--
History-aware progam computes the same as the history-agnostic program
-/
lemma sv0_eq_sv1 [dps : DPSystem ℕ] ε₁ ε₂ l : sv0_privMax ε₁ ε₂ l = sv1_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Initial setup is equal
  intro result
  simp [sv0_privMax, sv1_privMax]
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1

  -- unfold sum over product; term re. last sample should be equal as well
  conv =>
    congr
    · unfold sv0_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    · unfold sv1_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  apply tsum_congr
  intro vk

  -- LHS: simplify singleton sum
  conv =>
    enter [1, 1, a]
    simp [sv0_threshold]
  rw [ENNReal.tsum_eq_add_tsum_ite result]
  simp
  rw [@tsum_congr ENNReal ℕ _ _ _ (fun _ => 0) ?G1]
  case G1 =>
    intro
    split <;> simp
    rename_i H1
    intro
    exfalso
    apply H1
    symm
    trivial
  simp only [tsum_zero, add_zero]

  -- RHS: sum over all lists of length "result"
  -- Prove this by induction on result


  -- rw [tsum_ite_eq]
  sorry



/-
## Program version 2
  - Only moves the loop into a non-executable form, ie. explicitly defines the PMF
-/

def sv2_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
    return (sv1_threshold sk)
  computation point

lemma sv1_eq_sv2 [dps : DPSystem ℕ] ε₁ ε₂ l : sv1_privMax ε₁ ε₂ l = sv2_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro result
  simp [sv1_privMax, sv2_privMax]




/-
## Program version 3
  - Truncates the loop
-/

def sv3_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) (point + 1) ([], v0)
    return (sv1_threshold sk)
  computation point


-- Lemmas about cut loops

-- Loop cut to zero iterates is zero everywhere
lemma loop_cut_0_supp [dps : DPSystem ℕ] :
    (hist.length ≥ 0) ->
    probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) 0 ([], v0) (hist, vk) = 0 := by
  simp [probWhileCut]

-- loop cut to 1 is zero unless hist.length is 0
lemma loop_cut_1_supp [dps : DPSystem ℕ] :
    (hist.length ≥ 1) ->
    probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) 1 ([], v0) (hist, vk) = 0 := by
  intro H0
  simp [probWhileCut, probWhileFunctional]
  cases (sv1_privMaxC τ l ([], v0))
  · -- Loop check is false, returns ([], v0)
    simp
    intro H1
    cases H1
    simp at H0
  · -- Loop checks to true, passes to base case (prob_zero)
    simp

-- loop cut to 2 is zero unless the length is at most 1
lemma loop_cut_2_supp [dps : DPSystem ℕ] :
    (hist.length ≥ 2) ->
    probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) 2 ([], v0) (hist, vk) = 0 := by
  intro H0
  simp [probWhileCut, probWhileFunctional]
  cases (sv1_privMaxC τ l ([], v0))
  · -- Loop check is false, returns ([], v0)
    -- excluded by length hypothesis
    simp
    intro H1
    cases H1
    simp at H0
  -- loop check is true
  simp
  intro ⟨ hist1, v1 ⟩

  -- F is applied, always adds a single sample to the state
  cases (Classical.em (∃ v, hist1 = [v]))
  · -- F did add a single sample to the tape
    rename_i h
    rcases h with ⟨ v0, Hhist1 ⟩
    rw [Hhist1]
    right

    cases (sv1_privMaxC τ l ([v0], v1))
    · -- Check is false, returns ([v0], v1)
      -- Excluded by length hypothesis
      simp
      intro H1
      cases H1
      simp at H0

    · -- Check is true
      simp

  · -- F didn't add a single sample to the tape, is impossible
    -- FIXME: Refactor this out
    left
    rename_i h
    simp [sv1_privMaxF]
    intro v1 H
    exfalso
    apply h
    exists v0
    cases H
    rfl


lemma loop_cut_2_cut_1_eq_len_0 [dps : DPSystem ℕ] :
    (hist.length = 0) ->
    probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) 2 ([], v0) (hist, vk) =
    probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) 1 ([], v0) (hist, vk) := by
  intro H
  simp [probWhileCut, probWhileFunctional]
  cases (sv1_privMaxC τ l ([], v0))
  · -- First check is false
    -- Both sides step to probPure ([], v0), which are equal
    simp only [Bool.false_eq_true, ↓reduceIte]
  · -- First check is true
    -- RHS steps to probZero
    simp only [↓reduceIte, bind_apply, zero_apply, mul_zero, tsum_zero, ENNReal.tsum_eq_zero, mul_eq_zero]
    -- Apply F on the left-hand side
    intro ⟨ hist', v1 ⟩
    cases (Classical.em (∃ v, hist' = [v]))
    · right
      rename_i h
      rcases h with ⟨ h0, Hhist' ⟩
      -- We have already added too much to the history (since hist.lenght = 0)
      -- All cases from here on out are zero
      split <;> simp
      intro H2
      cases H2
      simp_all
    · -- F didn't add exactly one sample (impossible)
      left
      rename_i h
      simp [sv1_privMaxF]
      intro v1 H
      exfalso
      apply h
      exists v0
      cases H
      rfl


def cone_of_possibility (cut : ℕ) (initial hist : List ℤ) : Prop :=
  (hist.length < cut + initial.length) ∧ (initial.length ≤ hist.length)

def constancy_at [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) : Prop :=
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) (1 + cut) (initial, v0) (hist, vk) =
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut       (initial, v0) (hist, vk)


-- All points to the left of the cone are zero
lemma cone_left_zero [DPSystem ℕ] :
    hist.length < initial.length ->
    probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut (initial, v0) (hist, vk) = 0 := by
  sorry

-- All points below the cone are zero
lemma cone_below_zero [DPSystem ℕ] :
    cut + initial.length ≤ hist.length ->
    probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut (initial, v0) (hist, vk) = 0 := by
  revert initial v0 vk
  induction cut
  · simp [probWhileCut, probWhileFunctional]
  · rename_i cut' IH
    intro intial v0 vk Hcut'
    unfold probWhileCut
    unfold probWhileFunctional
    split <;> simp
    · intro h
      rcases h with ⟨ initial', vk' ⟩
      cases Classical.em (¬ ∃ v', initial' = intial  ++ [v'])
      · left
        simp [sv1_privMaxF]
        intro i Hi
        exfalso
        cases Hi
        rename_i h
        apply h
        exists v0
      rename_i h
      simp at h
      rcases h with ⟨ v', Hinitial' ⟩
      right
      apply IH
      simp_all
      linarith
    · intro H
      cases H
      simp at Hcut'

-- Base case: left edge of the cone satisfies constancy
lemma cone_left_edge_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
  sorry

lemma cone_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
  -- Need theorem to be true for all initial states, since this will increase during the induction
  -- v0 and vk will also change in ways which don't matter
  revert initial v0 vk

  induction cut
  · -- Not true base case (cut 0 is always outside of the cone)
    -- Mercifully it is easy to prove
    intro v0 vk initial Hcone
    unfold constancy_at
    simp [probWhileCut, probWhileFunctional]
    cases (sv1_privMaxC τ data (initial, v0)) <;> simp
    unfold cone_of_possibility at Hcone
    linarith

  rename_i n IH
  intro v0 vk initial Hcone
  -- True base case: are we on the left-hand edge of the cone
  cases Classical.em (hist.length = initial.length)
  · apply cone_left_edge_constancy <;> assumption

  -- If not, unfold the first (and only the first) level of the induction
  unfold constancy_at
  unfold probWhileCut
  unfold probWhileFunctional

  -- If the conditional is false, we are done
  cases (sv1_privMaxC τ data (initial, v0))
  · simp


  -- If the conditional is true, we decrement N by one and add a sample to the history
  rename_i Hcone_interior
  unfold constancy_at at IH
  simp
  apply tsum_congr
  intro ⟨ initial', vk' ⟩

  -- We only need to consider the cases where sv1_privMaxF is nonzero
  -- And this is exactly the case where initial' is initial plus one element
  simp [sv1_privMaxF]
  rw [← ENNReal.tsum_mul_right]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro z
  cases Classical.em (¬ ∃ v', initial' = initial ++ [v'])
  · split
    · exfalso
      rename_i h1 h2
      apply h1
      exists v0
      cases h2
      trivial
    · simp
  rename_i h
  simp at h
  rcases h with ⟨ v', Hinitial' ⟩
  split <;> try simp
  rename_i h
  cases h
  congr 1

  -- Apply the IH
  apply IH

  -- Prove that the new value is in the new cone of possibility
  unfold cone_of_possibility at Hcone
  rcases Hcone with ⟨ Hcone1, Hcone2 ⟩
  unfold cone_of_possibility
  apply And.intro
  · simp
    linarith
  · simp
    apply Nat.lt_iff_add_one_le.mp
    apply LE.le.eq_or_lt at Hcone2
    cases Hcone2
    · exfalso
      apply Hcone_interior
      symm
      trivial
    · trivial


-- Define cone
-- Define constancy, parameterized by initial list length
-- Prove zero for the region to the left of the cone (done before)
-- Prove zero for the region below the cone (done before)
-- Define base case in terms of cone
-- Prove base case in terms of cone
-- Prove inductive case for code








lemma sv2_eq_sv3 [dps : DPSystem ℕ] ε₁ ε₂ l : sv2_privMax ε₁ ε₂ l = sv3_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Step through equal headers
  intro point
  unfold sv2_privMax
  unfold sv3_privMax
  simp
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1
  apply tsum_congr
  intro final_state
  rcases final_state with ⟨ hist, vk ⟩
  split <;> try rfl
  rename_i H
  simp [H, sv1_threshold]
  clear H

  -- Apply a lemma about eventual constancy
  apply probWhile_apply
  apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ (hist.length + 1)
  intro i H

  sorry



/-
## Program version 4
  - Presamples each vk
  - Iteratively checks if the loop
  - Still loops through prefixes of the vk's iteratively
-/

-- Presamples the list (v_(n-1), v_(n-2), ..., v0)
def sv4_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang (List ℤ) := do
  match n with
  | Nat.zero => return []
  | (Nat.succ n') => do
      let v <- @privNoiseZero dps ε₁ (4 * ε₂)
      let l <- sv4_presample ε₁ ε₂ n'
      return (v :: l)

def sv4_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0) && sv4_evaluate_history vs τ l


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ (point + 1)
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv4_evaluate_history history τ l && (! sv1_privMaxC τ l (history, vk)))
       then return point
       else probZero
   computation point

lemma sv3_eq_sv4 [dps : DPSystem ℕ] ε₁ ε₂ l : sv3_privMax ε₁ ε₂ l = sv4_privMax ε₁ ε₂ l := by
  sorry





/-
## Program version 5
  - Presamples each vk
  - Performs a single check, rather than a loop
-/
def sv5_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0)

def sv5_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ (point + 1)
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv5_evaluate_history history τ l && (! sv1_privMaxC τ l (history, vk)))
       then return point
       else probZero
   computation point

lemma sv4_eq_sv5 [dps : DPSystem ℕ] ε₁ ε₂ l : sv4_privMax ε₁ ε₂ l = sv5_privMax ε₁ ε₂ l := by
  sorry
