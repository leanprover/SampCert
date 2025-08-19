import SampCert

/- A tactic is a proof strategy that can be applied to simplify a proof goal.
   In practice, proving a statement involves using a series to tactic to manipulate the
   proof state and reducing the goal to previously established theorems or hypotheses. -/

/- The simplest tactic is `rfl`, which handles definitional equality -/
lemma two_plus_two : 2 + 2 = 4 := rfl

/- Once we have the above lemma, we can use it to prove other lemmas: -/
lemma two_plus_two' : 4 = 2 + 2 := (Eq.symm two_plus_two)

lemma real_add_pres_eq (a b c : ℝ): a = b → a + c = b + c := by
  intro h
  rw [h]
  /- We could also do `rw[h]` instead of `rewrite`, which automatically uses `rfl` to close the goal -/

/- If our goal is `B`, and we know that `A → B` then the `apply` tactic says that it's enough to prove `A` -/
lemma silly_arithmetic (c : ℝ): (2 *2 - 1) + c = 3 + c := by
  apply real_add_pres_eq
  ring

/- Propositions are types in Lean! -/

def List.add_1_to_hd (l : List ℕ) (h : l ≠ []) := List.head l h + 1

/- First, notice that we are using a dependent type: List ℕ -/

/- What is the type of the function List.head_add_1? Is it List ℕ → List ℕ? -/

#check List.add_1_to_hd

/- `l ≠ []` is a type, and an inhabitant of this type is a proof that `l` is not empty! -/

theorem Fermat : ∀ (a b c : ℕ) (n : ℕ), n > 2 → a^n + b^n = c^n → False := sorry
