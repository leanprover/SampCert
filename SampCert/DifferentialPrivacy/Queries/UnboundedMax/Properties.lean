/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` reductions
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
  | (h :: hs) => G l ⟨ h :: hs , by simp ⟩ < τ



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
def privMax_eval_alt_F {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (history : List ℤ) : SLang (List ℤ) := do
  let candidate <- @privNoiseZero dps ε₁ (4 * ε₂)
  return history ++ [candidate]



/--
Support of privMaxEval_alt_body is contained in the extensions of the history by one element
-/
lemma privMaxEval_alt_body_supp {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) history eval :
    (@privMax_eval_alt_F dps ε₁ ε₂ history eval) ≠ 0 -> ∃ z, eval = history ++ [z] := by
  simp [privMax_eval_alt_F ]
  intro x Heval _
  exists x

-- FIXME: cleanup proof
lemma privMaxEval_alt_body_supp' {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) history eval :
    (¬(∃ z, eval = history ++ [z])) -> (@privMax_eval_alt_F dps ε₁ ε₂ history eval) = 0 := by
  apply Classical.by_contradiction
  intro A
  apply A
  intro B
  suffices ¬(privMax_eval_alt_F ε₁ ε₂ history eval ≠ 0) by
    exact False.elim (this fun a => A fun _ => a)
  intro C
  apply B
  apply privMaxEval_alt_body_supp ε₁ ε₂
  trivial


def privMax_eval_alt_loop {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang (List ℤ) := do
  probWhile
    (privMax_eval_alt_cond l τ)
    (@privMax_eval_alt_F dps ε₁ ε₂)
    []


/--
History-aware privMax program
-/
def privMax_eval_alt {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let final_history <- @privMax_eval_alt_loop dps ε₁ ε₂ l τ
  return final_history.length - 1

/-
## Reduction 0: The implementation version is the same as the history-tracking version


This reduction is not necessary, technically, since privMax_eval_alt is computable.
The later reductions, on the other hand, are necessary.
-/

lemma privMax_reduction_0 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_eval dps ε₁ ε₂ l = @privMax_eval_alt dps ε₁ ε₂ l := by
  unfold privMax_eval privMax_eval_alt
  simp
  apply funext
  intro N
  simp
  apply tsum_congr
  intro τ
  congr 1
  unfold privMax_eval_alt_loop
  conv =>
    enter [1, 1, a, 2]
    rw [ENNReal.tsum_prod']

  -- Separate the sum on the right into a sum over list lengths
  sorry




/-
## Reduction 1: The history-tracking version is the same as a bounded history-tracking version
-/


/--
Sampling loop for the bounded history-aware privMax function
-/
def privMax_eval_alt_loop_cut {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (N : ℕ) : SLang (List ℤ) := do
  probWhileCut
    (privMax_eval_alt_cond l τ)
    (@privMax_eval_alt_F dps ε₁ ε₂)
    (N + 1)
    []

/--
Closed form for privMax_eval_alt_loop_cut evaluated on the history hist, in terms of the number of iterates.

Namely, it is a step function. The function probWhileCut needs (hist.length + 1) iterates before hist
is in its support, and afterwards, no additional iterates return hist.
-/
def privMax_eval_alt_loop_cut_step {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (iterates : ℕ) (hist : List ℤ) : ENNReal :=
  if (iterates < hist.length)
    then 0
    else @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ hist.length hist


/--
Length of the supported region is bounded below by the length of the initial history.
-/
lemma privMax_eval_cut_supp_bound {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (A B : List ℤ) (HAB : A.length > B.length) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N A B = 0 := by
  revert A
  induction N
  · simp [probWhileCut]
  · intro A HA
    rename_i N' IH
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      intro F_A
      cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
      · rename_i h
        rcases h with ⟨ z, HF_A ⟩
        right
        apply IH
        simp [HF_A]
        linarith
      · left
        apply privMaxEval_alt_body_supp'
        trivial
    · simp
      intro HK
      simp [HK] at HA


/--
After a certain number of iterations, the function stops changing.
-/
lemma privMax_eval_cut_const_ind {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (B : List ℤ) (HN : B.length + 1 ≤ N) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N [] B =
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) (N + 1) [] B := by
  -- We should be able to prove this by rewriting into the split form, and then applying the strong
  -- congruence theorem with the support bound above.
  sorry




/--
Length of supported region is bounded abouve by the length of the initial history, plus the number of iterations.
-/
lemma privMax_eval_cut_supp_bound' {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (A B : List ℤ) (HAB : A.length + N < B.length + 1) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N A B = 0 := by
  revert A
  induction N
  · intro _ _
    simp [probWhileCut]
  · intro A HA
    rename_i N' IH
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      intro F_A
      cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
      · rename_i h
        rcases h with ⟨ z, HF_A ⟩
        right
        apply IH
        simp [HF_A]
        linarith
      · left
        apply privMaxEval_alt_body_supp'
        trivial
    · simp
      intro HK
      simp [HK] at HA


/--
Test lemma: privMax loop cut equals its closed form at []
-/
lemma privMax_eval_alt_loop_cut_closed_base {dps : DPSystem ℕ} :
    @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ N [] = @privMax_eval_alt_loop_cut_step dps ε₁ ε₂ l τ N [] := by
  -- Given the argument N = 0, the cut loop will do 1 iteration which is enough for [] to be stable.
  -- The step function will have threshold 0 < hist.length which will be false, so we get a stable value too.
  simp [privMax_eval_alt_loop_cut]
  simp [privMax_eval_alt_loop_cut_step]
  simp [privMax_eval_alt_loop_cut]

  simp [probWhileCut, probWhileFunctional]
  split
  · -- Loop does not terminate at the first conditional. We seek to show that the resulting distribution
    -- should not have [] in its support, because the first exit is the only time we return [].
    simp
    -- F_init is the result of the random sample (privMax_eval_alt_F ε₁ ε₂ [])
    intro F_init
    cases Classical.em (∃ z : ℤ, F_init = [z])
    · -- Case: F_init evaluates to the extension of [] by exactly one element
      right
      rename_i h
      rcases h with ⟨ z, hz ⟩
      subst hz
      -- We must show that probWhileCut starting with at least one element in the history
      -- never "rewrites history" to get back to [].
      apply privMax_eval_cut_supp_bound
      simp
    · -- Case: F_init does not evaluate to the extension of [] by exactly one element
      -- This has probability zero.
      left
      apply privMaxEval_alt_body_supp'
      simp only [List.nil_append]
      trivial
  · -- Loop does terminate at the first conditional
    simp


/--
privMax_eval_alt equals its closed form
-/
lemma privMax_eval_alt_loop_cut_closed {dps : DPSystem ℕ} :
    @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ N h = @privMax_eval_alt_loop_cut_step dps ε₁ ε₂ l τ N h := by
  unfold privMax_eval_alt_loop_cut_step
  split
  · -- Below the step
    unfold privMax_eval_alt_loop_cut
    apply privMax_eval_cut_supp_bound'
    simp
    trivial
  · -- Above the step

    -- Equal to the step point
    cases Classical.em (N = h.length)
    · rename_i Hn
      subst Hn
      rfl
    · -- Greater than the step point

      -- Cleanup context
      rename_i H1 H2
      have H3 : h.length < N := by
        apply lt_of_not_ge
        intro HK
        apply GE.ge.le at HK
        apply LE.le.eq_or_lt at HK
        cases HK <;> simp_all
      clear H1 H2

      induction N
      · exfalso
        simp at H3
      rename_i N' IH

      cases Classical.em (N' = h.length)
      · simp_all
        -- The real base case
        -- Should be basically the same as the other argument though
        -- Just can't/don't need to rewrite with the IH
        unfold privMax_eval_alt_loop_cut
        symm
        apply privMax_eval_cut_const_ind
        rfl
      rw [<- IH ?G1]
      case G1 =>
        apply Nat.lt_add_one_iff.mp at H3
        apply LE.le.eq_or_lt at H3
        cases H3 <;> simp_all

      unfold privMax_eval_alt_loop_cut
      symm
      apply privMax_eval_cut_const_ind
      linarith




/--
The first reduction: Evaluate each point using a finite number of iterates
-/
def privMax_eval_alt_cut {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := (fun N =>
  (do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let final_history <- @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ N
    return final_history.length - 1) N)

/-
The main program equals the cut program
-/
-- lemma privMax_eval_alt_loop_limit :

lemma privMax_reduction_1 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_eval_alt dps ε₁ ε₂ l = @privMax_eval_alt_cut dps ε₁ ε₂ l := by
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
  sorry
  -- rw [H, H]
  -- clear H

  -- rw [privMax_eval_alt_loop_cut_step, privMax_eval_alt_loop_cut_step]
  -- simp [Hcutoff]
  -- apply ite_congr ?G1 (congrFun rfl) (congrFun rfl)

  -- sorry







/-
## Reduction 2: The bounded history-tracking version is the same as a predicate on eager presample
-/

/--
Sample N noised values. Always returns a list of length N.
-/
def privMax_sampN {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // v.length = N } :=
  match N with
  | Nat.zero => probPure ⟨ [], by simp ⟩
  | Nat.succ N' => do
      let v <- @privNoiseZero dps ε₁ (4 * ε₂)
      let r <- @privMax_sampN dps ε₁ ε₂ N'
      probPure ⟨ v :: r.1, by cases r; simp ; trivial ⟩


/--
Sample N+1 noise values upfront. Return (N+1) when the first N noised prefix
sums are less than τ, and the N+1st noised prefix sum exceeds τ.
-/
def privMax_presample {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
(fun N =>
  (do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let history <- @privMax_sampN dps ε₁ ε₂ N.succ
    if (privMax_eval_alt_cond l τ history.1) ∧ ¬ (privMax_eval_alt_cond l τ history.1.tail)
      then probPure (N + 1)
      else probZero)
  N)



lemma privMax_reduction_2 {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ)  :
    @privMax_eval_alt_cut dps ε₁ ε₂ l = @privMax_presample dps ε₁ ε₂ l := by
  -- Evaluate the identical preludes
  unfold privMax_presample
  unfold privMax_eval_alt_cut
  apply SLang.ext
  intro N
  simp only [bind]
  congr 1
  apply funext
  intro τ



  sorry


/-
## Reduction 3: Separate the random samples we will view as deterministic, from the random samples for the DP proof.
-/


def privMax_presample_sep_det {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // v.length = N} :=
  @privMax_sampN dps ε₁ ε₂ N


def privMax_presample_sep {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
(fun N =>
  (do
    -- Part we will parameterize over (ie. using tsum_congr)
    let history <- @privMax_presample_sep_det dps ε₁ ε₂ N

    -- Part which includes the randomness in the proof (τ and the final sample)
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
    if (privMax_eval_alt_cond l τ (history.1 ++ [vk])) ∧ ¬ (privMax_eval_alt_cond l τ history.1)
      then probPure (N + 1)
      else probZero)
  N)



lemma privMax_reduction_3 {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_presample dps ε₁ ε₂ l = @privMax_presample_sep dps ε₁ ε₂ l := by
  unfold privMax_presample
  unfold privMax_presample_sep
  unfold privMax_presample_sep_det
  simp
  apply funext
  intro N

  sorry


def privMax_presample_sep_normalizes : HasSum (@privMax_presample_sep dps ε₁ ε₂ l) 1 := by
  rw [<- privMax_reduction_3]
  rw [<- privMax_reduction_2]
  rw [<- privMax_reduction_1]
  rw [<- privMax_reduction_0]
  exact privMaxPMF_normalizes


-- To express differential privacy, we need pricMax_presample_sep to be a PMF
def privMax_presample_sep_PMF {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℕ :=
  ⟨ @privMax_presample_sep dps ε₁ ε₂ l, privMax_presample_sep_normalizes ⟩



end SLang
