/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` Properties

This file proves pure DP for privMax, and zCDP for privMax using
the (ε^2/2)-zCDP bound.

privMax implemented using the abstract DP system, but I am not aware of how
to generalize the privacy proof to the abstract DP case.

Follows the proof given for Algorithm 1 pp. 57 "The Sparse Vector Technique"
in "The Algorithmic Foundations of Differential Privacy", Dwork & Roth.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang



/-
# Loop unrolling lemmas

`probWhileSplit cond body continuation n` is an n-unrolling of a loop, where `continuation` is
      applied in the case that n is exhaused.

`probWhileCut cond body n` is a `probWhileSplit` with continuation zero.

`probWhileSplit .. continuation (m + n)` is the same as `probWhileSplit .. .. m` with a
    `probWhileSplit .. continuation n` continuation.

`probWhileSplit .. probPure (m + n)`  is the same as `probWhileSplit .. probPure m` bound to
    `probWhileSplit .. probPure b`.

`probWhileSplit .. probZero (m + n)`  is the same as `probWhileSplit .. probPure m` bound to
    `probWhileSplit .. probZero b`, provided `n > 0`. This last lemma enables us to separate
    the first m unrollings of a nontrivial probWhile loop.

The helper function `probBind_congr_strong` enables us to restruct congruence proofs between
    probBind programs to their support.

The predicate
-/

/--
Stronger congruence rule for probBind: The bound-to functions have to be equal only on the support of
the bound-from function.
-/
lemma probBind_congr_strong (p : SLang T) (f : T -> SLang U) (g : T -> SLang U) (Hcong : ∀ t : T, p t ≠ 0 -> f t = g t) :
    p >>= f = p >>= g := by
  simp
  unfold probBind
  apply SLang.ext
  intro u
  apply Equiv.tsum_eq_tsum_of_support ?G1
  case G1 =>
    apply Set.BijOn.equiv (fun x => x)
    simp [Function.support]
    have Heq : {x | ¬p x = 0 ∧ ¬f x u = 0} =  {x | ¬p x = 0 ∧ ¬g x u = 0} := by
      apply Set.sep_ext_iff.mpr
      intro t Ht
      rw [Hcong]
      apply Ht
    rw [Heq]
    apply Set.bijOn_id
  simp [Function.support]
  intro t ⟨ Hp, _ ⟩
  simp [Set.BijOn.equiv]
  rw [Hcong]
  apply Hp



/--
``SLang`` value obtained by applying a loop body exactly ``n`` times to a given distribution
-/
def probWhileSplit (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => continuation a
  | Nat.succ n => do
    if cond a
      then
        let v ← body a
        probWhileSplit cond body continuation n v
      else
        return a


/--
probWhileCut is probWhileSplit applied to the zero distribution
-/
lemma probWhileCut_probWhileSplit_zero (cond : T → Bool) (body : T → SLang T) (n : Nat) :
    probWhileCut cond body n = probWhileSplit cond body (fun _ => probZero) n := by
  apply funext
  induction n
  · simp [probWhileCut, probWhileSplit]
  · rename_i n IH
    simp [probWhileCut, probWhileSplit]
    rw [funext IH]
    intro _
    rfl

/--
Evaluate probWhileSplit when out of steps
-/
lemma probWhileSplit_zero (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (init : T):
    probWhileSplit cond body continuation 0 init = continuation init := by
  simp [probWhileSplit]

/--
probWhileSplit is constant when the condition is false
-/
lemma probWhileSplit_cond_false_cst (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T)
    (n : Nat) (init : T) (HF : cond init ≠ true) :
    probWhileSplit cond body continuation (Nat.succ n) init =
    probPure init := by
  rw [probWhileSplit]
  split
  · exfalso
    simp_all
  rfl

/--
Move an iterate of of probWhileSplit into the continuation.
-/
lemma probWhileSplit_succ_l (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (n : Nat) (init : T):
    probWhileSplit cond body continuation (Nat.succ n) init =
    (probWhileSplit cond body (probWhileSplit cond body continuation n) 1 init) := by
  apply funext
  intro _
  simp [probWhileSplit]

/--
Move multiple iterates of of probWhileSplit into the continuation.
-/
lemma probWhileSplit_add_l (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (m n : Nat) (init : T):
    probWhileSplit cond body continuation (n + m) init =
    (probWhileSplit cond body (probWhileSplit cond body continuation n) m init) := by
  revert init
  induction m
  · intro init
    rw [probWhileSplit_zero]
    simp only [add_zero]
  · intro init
    rename_i m' IH
    rw [probWhileSplit_succ_l]
    rw [<- (funext IH)]
    rw [<- probWhileSplit_succ_l]
    rfl


/--
Move iterate of probWhileSplit into the initial value, when the continuation is probPure
-/
lemma probWhileSplit_succ_r_pure (cond : T → Bool) (body : T → SLang T) (n : Nat) (init : T):
    probWhileSplit cond body probPure (Nat.succ n) init =
    (probWhileSplit cond body probPure 1 init)  >>=  (probWhileSplit cond body probPure n) := by
  apply funext
  intro x
  have H : (probWhileSplit cond body probPure 1 init) = if (cond init) then (body init) >>= probPure else pure init := by
    apply funext
    intro x
    rw [probWhileSplit]
    split
    · simp [probWhileSplit]
    · rfl
  rw [H]
  simp only [probWhileSplit]
  split
  · simp
  · have H : (pure init >>= probWhileSplit cond body probPure n) = pure init := by
      apply funext
      intro x
      simp [pure_apply]
      conv =>
        lhs
        enter [1, a]
      rw [ENNReal.tsum_eq_add_tsum_ite init]
      simp
      cases n
      · simp [probWhileSplit]
        rw [ENNReal.tsum_eq_zero.mpr ?G1]
        case G1 =>
          intro i
          split <;> rfl
        simp
      · rename_i n'
        rw [probWhileSplit_cond_false_cst _ _ _ _ _ (by trivial)]
        simp [probPure]
        rw [ENNReal.tsum_eq_zero.mpr ?G1]
        case G1 =>
          intro i
          split <;> rfl
        simp
    rw [H]


/--
Move iterates of probWhileSplit into the initial value, when the continuation is probPure
-/
lemma probWhileSplit_add_r_pure (cond : T → Bool) (body : T → SLang T) (m n : Nat) (init : T):
    probWhileSplit cond body probPure (m + n) init =
    (probWhileSplit cond body probPure m init)  >>=  (probWhileSplit cond body probPure n) := by
  revert init
  induction m
  · simp [probWhileSplit]
  · intro init
    rename_i m' IH
    rw [add_comm, <- add_assoc]
    rw [probWhileSplit_succ_r_pure]
    rw [add_comm]
    rw [bind_congr IH]
    rw [probWhileSplit_succ_r_pure _ _ m']
    conv =>
      congr
      · enter [1]
        simp [probWhileSplit]
      · enter [1, 1]
        simp [probWhileSplit]
    split <;> simp




/--
Move iterate of probWhileSplit into initial condition, when continuation is probZero
-/
lemma probWhileSplit_succ_r_zero (cond : T → Bool) (body : T → SLang T) (n : Nat) (Hn : n > 0) (init : T):
    probWhileSplit cond body (fun _ => probZero) (Nat.succ n) init =
    (probWhileSplit cond body probPure 1 init)  >>=  (probWhileSplit cond body (fun _ => probZero) n) := by
  apply funext
  intro x
  simp [probWhileSplit]
  split
  · simp [probBind]
  · rename_i h
    simp at h
    conv =>
      rhs
      enter [1, a]
      simp [probPure]
    rw [ENNReal.tsum_eq_add_tsum_ite init]
    simp
    have H1 :
      (∑' (x_1 : T), if x_1 = init then 0 else if x_1 = init then probWhileSplit cond body (fun _ => probZero) n x_1 x else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro i
      split <;> simp
    simp [H1]
    clear H1
    unfold probWhileSplit
    cases n
    · exfalso
      linarith
    · simp [h]


/--
Move iterate of probWhileSplit into initial condition, when continuation is probZero
-/
lemma probWhileSplit_add_r_zero (cond : T → Bool) (body : T → SLang T) (m n : Nat) (Hn : n > 0) (init : T):
    probWhileSplit cond body (fun _ => probZero) (m + n) init =
    (probWhileSplit cond body probPure m init)  >>=  (probWhileSplit cond body (fun _ => probZero) n) := by
  revert init
  induction m
  · intro init
    simp [probWhileSplit]
  · intro init
    rename_i m' IH
    conv =>
      lhs
      rw [add_comm, <- add_assoc]
    rw [probWhileSplit_succ_r_zero _ _ _ (by linarith)]
    rw [add_comm]
    cases m'
    · simp
    rename_i m''
    rw [bind_congr IH]
    clear IH
    unfold probWhileSplit
    simp
    split <;> simp
    · rename_i h
      apply probBind_congr_strong
      intro t _
      simp [probWhileSplit]
    · rw [if_neg (by trivial)]
      simp

/--
Separate out the first m unrollings of a nontrivial probWhileCut loop
-/
theorem probWhileCut_add_r (cond : T → Bool) (body : T → SLang T) (m n : Nat) (Hn : n > 0) (init : T):
    probWhileCut cond body (m + n) init =
    (probWhileSplit cond body probPure m init) >>= (probWhileCut cond body n) := by
  rw [probWhileCut_probWhileSplit_zero]
  rw [probWhileCut_probWhileSplit_zero]
  apply probWhileSplit_add_r_zero
  trivial



lemma unfunext (f g : A -> B) (a : A) (H : f = g) : f a = g a := by
  subst H
  rfl


-- theorem probWhileCut_eventually_constant (cond : T → Bool) (body : T → SLang T) (i n : Nat) (Hn : 0 < n) (init : T)
--     (p : T)
--     -- Evaluating at p for n iterates, the base case isn't relevant
--     -- Basically, after n iterates, nothing touches the point p
--     (Hno_base : probWhileCut cond body n init p = probWhileSplit cond body probPure n init p)
--
--     -- This is too strong
--     -- -- The continue condition will be false for everything in the support of the first n iterates?
--     -- (Hterm : ∀ t : T, probWhileSplit cond body probPure n init t ≠ 0 -> cond v = false ) :
--
--     -- Starting at anything in the support of the first t iterates, any additional iterates won't change p
--     -- This is also too strong, since the first t iterates can terminate early.
--     -- (Hsep : ∀ t : T, probWhileSplit cond body probPure n init t ≠ 0 -> True) :
--
--     -- Two ideas:
--     --   - Develop equations for "doing exactly n iterations"
--     --   - Strengthen monotone condition predicate to decide if the first n iterates terminated
--     --     successfully or hit the base case
--
--     -- In order to finish this lemma, we need to say that either:
--     --   - The first n iterates don't terminate early, putting us in a state when
--     --        future iterates don't touch the evaluation at p.
--     --   - The first n iterates do terminate early; putting us in a state
--     --        where any hypothetical future iterate will fail the check (cond monotonicity)
--     --        so will not touch the evaluation at p.
--     -- This is pretty challenging to express without being able to index into the loop guards.
--     -- So it may be easier to leave as is, and prove it only for our special case, where tracking
--     -- histories makes this possible.
--     :
--     probWhileCut cond body (n + i) init p = probWhileCut cond body n init p := by
--   cases i
--   · simp
--   rename_i i'
--   rw [probWhileCut_add_r _ _ _ _ (by linarith)]
--   rw [Hno_base]
--
--   have H : probWhileSplit cond body probPure n init p = (probWhileSplit cond body probPure n init >>= probPure) p := by
--     simp [probWhileSplit]
--
--     sorry
--   rw [H]
--   simp only [bind]
--
--   -- For all values in the support of the first n iterates, trying to do more iterates will terminate immediately
--   apply (unfunext _ _  p (probBind_congr_strong _ _ _ _))
--   intro v Hv
--   -- simp only [probWhileCut, probWhileFunctional]
--
--   sorry

-- -- A conditional is monotone if, as soon as it becomes False, it remains false on the entire support
-- -- of the body.
-- def mono_conditional (cond : T → Bool) (body : T → SLang T) : Prop :=
--     ∀ t : T, (cond t = false) -> (∀ t', cond t' = false ∨ body t t' = 0)







/-
## History-tracking privMax program
-/


/--
G: Maximum noised prefix sum.

vis is a fixed list of noise samples.
-/
def G (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) : ℤ :=
  let vis' := (List.mapIdx (fun i vi => exactDiffSum i l + vi) vis)
  let Hvis' : 0 < vis'.length := by
    dsimp [vis']
    cases vis
    simp [List.length_mapIdx]
    trivial
  List.maximum_of_length_pos Hvis'


/--
Adding additional random samples (thereby extending the prefix sum) can only increase the value of G
-/
lemma G_mono (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) (c : ℤ) pf :
    G l vis ≤ G l ⟨ vis.1 ++ [c], pf ⟩ := by
  simp [G]
  apply List.maximum_le_of_forall_le
  intro a Ha
  apply List.le_maximum_of_mem'
  rw [List.mapIdx_append_one]
  rw [List.mem_append]
  left
  trivial




/--
History-aware loop condition for the privMax program

Monotonicity allows us to express this in terms of the entire history. The imlemented
version shoudld only consider the last sample.
-/
def privMax_eval_alt_cond (l : List ℕ) (τ : ℤ) (history : List ℤ) : Bool :=
  match history with
  | [] => true
  | (h :: hs) => G l ⟨ h :: hs, by simp ⟩ < τ



/--
Once a history terminates the loop, any hypothetical future loop conditions are also aware that it terminates
-/
lemma privMax_G_continue_alt_mono (l : List ℕ) (τ : ℤ) (history : List ℤ) (future : ℤ) :
    ¬ privMax_eval_alt_cond l τ history -> ¬ privMax_eval_alt_cond l τ (history ++ [future]):= by
  unfold privMax_eval_alt_cond
  cases history
  · simp
  rename_i a b
  simp only [decide_eq_true_eq, List.cons_append]
  intro H1 H2
  apply H1
  apply LE.le.trans_lt _ H2
  apply G_mono



/--
History-aware body for the privMax sampling loop
-/
def privMax_eval_alt_F (ε₁ ε₂ : ℕ+) (history : List ℤ) : SLang (List ℤ) := do
  let candidate <- privNoiseZero ε₁ (4 * ε₂)
  return history ++ [candidate]



/--
Support of privMaxEval_alt_body is contained in the extensions of the history by one element
-/
lemma privMaxEval_alt_body_supp (ε₁ ε₂ : ℕ+) history eval :
    (privMax_eval_alt_F ε₁ ε₂ history eval) ≠ 0 -> ∃ z, eval = history ++ [z] := by
  simp [privMax_eval_alt_F ]
  intro x Heval _
  exists x



def privMax_eval_alt_loop (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang (List ℤ) := do
  probWhile
    (privMax_eval_alt_cond l τ)
    (privMax_eval_alt_F ε₁ ε₂)
    []
    -- (<- privMax_eval_alt_F ε₁ ε₂ [])

/--
History-aware privMax program
-/
def privMax_eval_alt (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let final_history <- privMax_eval_alt_loop ε₁ ε₂ l τ
  return final_history.length

/--
Sampling loop for the bounded history-aware privMax function
-/
def privMax_eval_alt_loop_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (N : ℕ) : SLang (List ℤ) := do
  probWhileCut
    (privMax_eval_alt_cond l τ)
    (privMax_eval_alt_F ε₁ ε₂)
    N
    []


/--
Closed form for privMax_eval_alt_loop_cut evaluated on the history hist, in terms of the number of iterates.

Namely, it is a step function.
-/
def privMax_eval_alt_loop_cut_step (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (iterates : ℕ) (hist : List ℤ) : ENNReal :=
  if (iterates < hist.length)
    then 0
    else privMax_eval_alt_loop_cut ε₁ ε₂ l τ hist.length hist


/--
privMax_eval_alt equals its closed form
-/
lemma privMax_eval_alt_loop_cut_closed :
    privMax_eval_alt_loop_cut ε₁ ε₂ l τ N h =  privMax_eval_alt_loop_cut_step ε₁ ε₂ l τ N h := by
  revert h
  induction N
  · intro h
    simp [privMax_eval_alt_loop_cut, privMax_eval_alt_loop_cut_step]
    simp [probWhileCut]
    cases h <;> simp
    simp [probWhileCut]
  rename_i N' IH



  sorry


/--
The first reduction: Evaluate each point using a finite number of iterates
-/
def privMax_eval_alt_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := (fun N =>
  (do
    let τ <- privNoiseZero ε₁ (2 * ε₂)
    let final_history <- privMax_eval_alt_loop_cut ε₁ ε₂ l τ N
    return final_history.length) N)

/-
The main program equals the cut program
-/
-- lemma privMax_eval_alt_loop_limit :

lemma privMax_reduction_1 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    privMax_eval_alt ε₁ ε₂ l = privMax_eval_alt_cut ε₁ ε₂ l := by
  -- Want to show that the eval (unbounded at each point) equals the cut version (cut to N at each point)
  apply SLang.ext
  intro cutoff
  simp [privMax_eval_alt, privMax_eval_alt_cut]
  apply tsum_congr
  intro initial_point
  congr
  apply funext
  -- Loop should be the same evaluated at every history whose length is equal to cutoff
  intro evaluated_history
  split <;> try simp
  rename_i Hcutoff
  simp [privMax_eval_alt_loop, privMax_eval_alt_loop_cut]

  -- Apply probWhile limit lemma
  apply probWhile_apply
  apply (@tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ cutoff)

  -- Prove that probWhileCut is eventually constant
  intro later_cutoff Hlep
  rw [<- Nat.add_sub_cancel' Hlep]

  -- Change of variables
  generalize Hd : later_cutoff - cutoff = d
  clear Hlep Hd later_cutoff

  -- Change to closed form
  have H := @privMax_eval_alt_loop_cut_closed
  unfold privMax_eval_alt_loop_cut at H
  rw [H, H]
  clear H

  rw [privMax_eval_alt_loop_cut_step, privMax_eval_alt_loop_cut_step]
  simp [Hcutoff]






/-
-- Reduction 2: Sample all the noise upfront (that is, calculate G(D)), and then
-- Check to see if the nth iterate is the terminating one.

def privMax_sampN (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // N = v.length } :=
  match N with
  | Nat.zero => probPure ⟨ [], by simp ⟩
  | Nat.succ N' => do
      let v <- privNoiseZero ε₁ (4 * ε₂)
      let r <- privMax_sampN ε₁ ε₂ N'
      probPure ⟨ v :: r.1, by cases r; simp ; trivial ⟩

-- A length N list only happens when we sample exactly N times,
-- Everyting up to the N-1th time did not terminate, and the Nth time did terminate.
-- (Put this in a probUntil to normalize)
def privMax_eval_alt_loop_cut_presample (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang ℕ :=
  fun N =>
    ((do
        let candidate <- (privNoiseZero ε₁ (4 * ε₂))
        let history <- privMax_sampN ε₁ ε₂ (N + 1)
        -- let GD_tau := G l ⟨ history, sorry ⟩--
        probPure 0) N)
  --  >>= (fun candidate => sorry)) N)


-- do
--   let history <-
--   let candidate <- privNoiseZero ε₁ (4 * ε₂)
--   if sorry
--     then probPure sorry -- history
--     else sorry -- probZero?? What?



def prefixes {T : Type*} (L : List T) : List (List T) := List.map (flip List.take L) $ List.range (L.length).succ


-- -- 1st reduction: Pointwise bound on the number of loop iterates
-- def privMax_eval_alt_loop_cut_simpler (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (N : ℕ) : SLang (List ℤ) := do
--   (fun history =>
--     ((do
--       for p in prefixes history do
--         (fun x => probPure [])
--       probPure [])
--     history))
--   -- probWhileCut
--   --   (privMax_eval_alt_cond l τ)
--   --   (privMax_eval_alt_F ε₁ ε₂)
--   --   N
--   --   (<- privMax_eval_alt_F ε₁ ε₂ [])




-- New idea:
-- Since the if condition is monotonic, we don't need to exit the while loop early.
-- The stopping condition does not have to depend on the state, and that has the potential
-- to simplify a ton of the things I'm getting stuck on.



-- Basically the same as probWhileFunctional, but it
--    - always applies the body
--    - keeps track of the current index
-- def probFor (body : ℕ -> T → SLang T) (index : ℕ) (init: T) : SLang T :=
--   match index with
--   | Nat.zero => return init
--   | Nat.succ N' => do
--     let init' <- body N' init
--     probFor body N' init'
--
--
-- def probWhile_of_probFor  (body : ℕ -> T → SLang T) (index : ℕ) (init: T) : SLang T :=
--   (probWhileCut
--     (fun (i, _) => i > 0)
--     (fun (i, t) => do return (i - 1, <- body i t))
--     (index + 1)
--     ((index : ℕ), (init : T))) >>= (fun z => return z.2)
--
--
-- def probFor_probWhileFunctional_eq (body : ℕ -> T → SLang T) (index : ℕ) (init: T) :
--   probFor body index init = probWhile_of_probFor body index init := by
--   revert init
--   induction index
--   · intro init
--     simp [probFor, probWhile_of_probFor, probWhileCut, probWhileFunctional]
--   · intro init
--     rename_i index' IH
--     simp [probFor]
--
--     sorry



-- Actually, might not even need to do this. For well behaved conditionals, I should be able to rewrite
-- it into this form without defining separate syntax?

lemma probWhileCut_monotone_lemma (cond : T → Bool) (body : T → SLang T)
    (n : Nat) (init : T) :
    probWhileCut cond body n init =
    (probWhileCut
      (fun (i, _) => i < n)
      (fun (i, t) => do if cond t then return (i + 1, <- body t) else return (i + 1, t))
      n
      (0, init)) >>= (fun x => x.1) := by
  revert init
  induction n
  · intro init
    simp [probWhileCut]
    unfold probZero
    unfold probBind
    simp
  · intro init
    rename_i n' IH
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      sorry
    · simp
      sorry



-- prove that the limit of probFor is a probWhile, for certain monotone predicates



-/

end SLang




-- Junk?
-- I might eventually want to use some of these definitions when proving the
-- equivalence to the non-history program


-- /--
-- privMax unrolled at most k times
-- -/
-- def privMax_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) (N : ℕ) : SLang ℕ := do
--   let τ <- privNoiseZero ε₁ (2 * ε₂)
--   let v0 <- privNoiseZero ε₁ (4 * ε₂)
--   let r <- (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N (0, v0))
--   return r.1
--
--
-- lemma privMax_cut_loop_0 (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (init : ℕ × ℤ) :
--     probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) 0 init = probZero := by
--   simp [probWhileCut]
--
-- /--
-- Move one iterate from a probWhileCut out to a probWhileSplit
--
-- MARKUSDE: We probably want the other direction: moving into init
-- -/
-- lemma privMax_cut_loop_succ_l (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N : ℕ) (init : ℕ × ℤ) :
--     probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) (Nat.succ N) init =
--     probWhileSplit (privMaxC τ l) (privMaxF ε₁ ε₂) (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N) 1 init := by
--   simp [probWhileCut, probWhileFunctional, probWhileSplit]
--
-- /--
-- Separate the first N iterates from probMax_cut:
-- Do n iterates inside a probWhileSplit, and the remaining M iterates inside probWhileCut
-- -/
-- lemma privMax_cut_loop_add_l (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N M : ℕ) (init : ℕ × ℤ) :
--     probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) (N + M) init =
--     probWhileSplit (privMaxC τ l) (privMaxF ε₁ ε₂) (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N) M init := by
--   revert init
--   induction N
--   · intro init
--     simp [probWhileCut]
--     rw [probWhileCut_probWhileSplit_zero]
--   · intro init
--     rename_i N' IH
--     rw [add_assoc, add_comm, add_assoc, add_comm]
--     rw [privMax_cut_loop_succ_l]
--     rw [add_comm]
--     rw [funext IH]
--     rw [(funext (privMax_cut_loop_succ_l _ _ _ _ _))]
--     rw [<- probWhileSplit_add_l]
--     rw [<- probWhileSplit_add_l]
--     rw [add_comm]
--
--
-- /--
-- Boundary of the support of the privMax_cut loop:
-- If we start in state (N, ?), for any k, (N + K + 1) will be zero after K steps.
-- ie. We step zero times, (N + 0 + 1) = N and beyond is still zero (since it starts with zero distribution)
--      We step two times, (N + 2) and beyond is zero.
-- -/
-- lemma privMax_cut_loop_support_bound (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (K N : ℕ) (vp: ℤ) (vi : ℤ)  :
--     probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) K (N, vi) (N + K, vp) = 0 := by
--   revert vi vp
--   induction K
--   · -- Exact boundary
--     induction N <;> simp [probWhileCut]
--   · rename_i K' IH
--     induction N
--     · sorry
--     · rename_i N' IH'
--       intro vp vi
--       simp [probWhileCut, probWhileFunctional]
--       split
--       · simp
--         simp at *
--         rename_i H
--         intro a b
--         simp [privMaxF]
--         have Ha : a ≠ N' + 1 + 1 := by sorry
--         right
--         have IH := IH vp vi
--         -- This is not helping
--         sorry
--       · simp
--      -- Lost



-- /--
-- Support of privMax_cut is bounded abouve by the cut number
-- -/
-- lemma privMax_cut_support_le_k (ε₁ ε₂ : ℕ+) (l : List ℕ) (N K : ℕ) :
--     privMax_cut ε₁ ε₂ l N (N + K) = 0 := by
--   simp [privMax_cut]
--   intro τ
--   right
--   intro v0
--   right
--   intro r vr Hr
--   subst Hr
--
--   -- The condition itself does not matter to this proof
--   generalize HC : (fun (x : ℕ × ℤ) => decide (exactDiffSum x.1 l + x.2 < τ)) = C
--   clear HC
--   rw [probWhileCut_probWhileSplit_zero]
--   revert v0 N
--   induction K
--   · intros N v0
--     simp
--     -- Equality case. Hmm.
--     sorry
--   · intros N v0
--     rename_i K' IH
--     have IH := IH N v0
--
--     sorry
--
--   -- -- Am I inducting on the wrong thing?
--   -- induction N
--   -- · aesop
--   -- · rename_i N' IH
--   --   intro K v0
--
--   --   -- Same as doing 1 iteration and then N' iterations
--   --   rw [probWhileSplit_succ_l]
--   --   simp [probWhileSplit]
--   --   split
--   --   · simp
--   --     intro v1
--   --     right
--   --     rw [<- IH K v1]
--
--   --     -- Need a shifting lemma
--
--   --     -- Err... the shifting lemma might not be provable
--   --     -- Because the condition depends on the start value
--
--   --     -- Incremeting the start condition just shifts the final distribution
--   --     -- Simplify irrelevant the expression for quality of life
--   --     generalize HF : (fun (x : ℕ × ℤ) => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) = F
--   --     conv =>
--   --       enter [1, 6, 1]
--   --       rw [add_comm]
--   --       rw [<- add_assoc]
--   --       enter [1]
--   --       rw [add_comm]
--   --     generalize HD : (N' + K) = D
--   --     clear HD
--   --     clear IH
--   --     induction N'
--   --     · simp [probWhileSplit]
--   --     · rename_i N'' IH''
--   --       conv =>
--   --         enter [1]
--   --         rw [probWhileSplit_succ_l]
--   --       rw [probWhileSplit_succ_l]
--   --       simp [probWhileSplit]
--   --       sorry
--   --   · simp



-- Since the max returnable value increases by at most 1 every iteration, and
--    privMaxCut _ _ _ 0 = (fun _ => 0),
-- we should be able to prove that for all N ≥ K ≥ 0
--   privMaxCut _ _ _ N K = 0



-- /--
-- privMax_cut is eventually constant (at every point N, it is constant after N terms).
-- -/
-- lemma privMax_cut_support_eventually_constant (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N K : ℕ) (VN : ℤ) :
--     probWhileCut (privMaxC τ l)
--       (fun x => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) (N + K) (0, v0) (N, VN) =
--     probWhileCut (privMaxC τ l)
--       (fun x => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) N (0, v0) (N, VN) := by
--
--   rw [probWhileCut_probWhileSplit_zero]
--   rw [probWhileCut_probWhileSplit_zero]
--
--   -- Induction: Reduce from (... N + K) to (... N + 1)
--   induction K
--   · simp
--   · rename_i K' IH
--     conv =>
--       enter [1, 4]
--       rw [<- add_assoc]
--     rw [probWhileSplit_succ_l]
--     generalize HF : (fun (x : ℕ × ℤ) => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) = F
--     rw [HF] at IH
--     rw [<- IH]
--     rw [<- probWhileSplit_succ_l]
--
--     -- Split it up into the first N terms, and the remaining K' or K'+1 terms in the contiunation
--     -- The "extra branches" should all be 0 when evaluated at N, their initial values all start higher than N.
--
--
--     -- FIXME: Actually do this step to make sure the lemmas I'm trying to prove are the right ones.
--
--     sorry
--
--
--
-- -- This can be used in a lemma to show that it's eventually constant, ie
-- -- for all N ≥ S k:
-- --    privMaxCut _ _ _ (N + 1) k = privMaxCut _ _ _ N k
--
--
-- -- This is because, if we do more unrollings, it just adds more branches
-- -- into a paths which all return values greater than k, by the lemma before.
--
-- -- Then, there should be a lemma about the limits of eventually constant sequences, which
-- -- alongside probWhile_apply, should be able to rewrite
-- --  privMax ... k = (let τ <- ..., privMax_cut ... k k)
-- lemma privMax_eval_limit {ε₁ ε₂ : ℕ+} {l : List ℕ} {k : ℕ} :
--     @privMax_eval PureDPSystem ε₁ ε₂ l k = privMax_cut ε₁ ε₂ l k k := by
--   simp [privMax_eval, privMax_cut]
--   apply tsum_congr
--   intro τ
--   congr 1
--   apply tsum_congr
--   intro v0
--   congr 1
--   apply tsum_congr
--   intro (r, vr)
--   split <;> try simp
--   rename_i Hk
--   subst Hk
--   apply probWhile_apply
--
--   -- Evaluate the filter
--   apply (@tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ k)
--   intro i Hi
--   rw [<- Nat.add_sub_cancel' Hi]
--   apply (@privMax_cut_support_eventually_constant v0 ε₁ ε₂ τ l k (i - k) vr)
