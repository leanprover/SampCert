import Mirror.H1
import Mathlib.Probability.Independence.Basic

open Classical Set Function ProbabilityTheory Nat

section Hurd

variable {T U : Type}
variable [MeasurableSpace T] [MeasurableSpace U]

def Hurd (T: Type) : Type := BitStream → T × BitStream

instance H : Monad Hurd where
  pure := λ { T : Type } => λ x : T => λ s : BitStream => (x,s)
  bind := λ { T U : Type } => λ f : Hurd T => λ g : T → Hurd U => λ s : BitStream => let (v,s') := f s ; (g v) s'


theorem Pure1 (x : T) (s : BitStream) : (H.pure x s).1 = x := sorry

def Coin : Hurd Bool := λ s : BitStream => (s 0, λ n : Nat => s (n + 1))

def strongly_measurable (f : Hurd T) : Prop :=
  Countable { y : T | exists (x : BitStream), y = (Prod.fst ∘ f) x } ∧ Measurable (Prod.fst ∘ f) ∧ Measurable (Prod.snd ∘ f)

@[simp]
theorem Meas1 (x : T) : strongly_measurable (H.pure x)  := sorry

@[simp]
theorem Meas2 (f: Hurd T) (g : T → Hurd U) :
  strongly_measurable f → (∀ x : T, strongly_measurable (g x)) →
  strongly_measurable (H.bind f g) := sorry

@[simp]
theorem Meas3 : strongly_measurable Coin := sorry

def independent (f : Hurd T) : Prop :=
  IndepSets ((λ A : Set T => (Prod.fst ∘ f)⁻¹' A) '' univ) ((λ A : Set BitStream => (Prod.snd ∘ f)⁻¹' A) '' univ) Prob.volume

def prefix_cover (C : Set (List Bool)) : Prop :=
  (∀ l₁ l₂ : List Bool, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂ → ¬ l₁ <+: l₂)
  ∧ Prob.volume (⋃ l ∈ C, prefix_set l) = 1

def strongly_independent (f : Hurd T) : Prop :=
  strongly_measurable f
  ∧ exists C : Set (List Bool), prefix_cover C
    ∧ ∀ (l : List Bool) (s : BitStream), l ∈ C ∧ s ∈ prefix_set l
      → f s = (Prod.fst (f (prefix_seq l)), sdrop (List.length l) s)

@[simp]
theorem indep (f : Hurd T) : strongly_independent f → independent f := sorry

@[simp]
theorem Indep1 (x : T) : strongly_independent (H.pure x)  := sorry

@[simp]
theorem Indep2 (f: Hurd T) (g : T → Hurd U) :
  strongly_independent f → (∀ x : T, strongly_independent (g x)) →
  strongly_independent (H.bind f g) := sorry

@[simp]
theorem Indep3 : strongly_independent Coin := sorry

def prob_while_cut (cond : T → Bool) (body : T → Hurd T) (n : Nat) (a : T) : Hurd T :=
  match n with
  | zero => H.pure a
  | succ n => if cond a then
    do let v ← body a
       prob_while_cut cond body n v
    else H.pure a

theorem PWC1 (cond : T → Bool) (body : T → Hurd T) (n : Nat) (a : T) :
  (∀ a : T, strongly_independent (body a)) →
  strongly_independent (prob_while_cut cond body n a) := sorry

-- Smallest n that satisfies f
noncomputable def minimal (f : Nat → Bool) : Nat := sorry

-- Odd because no value is returned, but the new RNG is
noncomputable def prob_while1 (cond : T → Bool) (body : T → Hurd T) (a : T) (s : BitStream) : Hurd (Option T) :=
  if (∃ n : Nat, ¬ cond ((prob_while_cut cond body n a s).1))
  then
  do let v ← prob_while_cut cond body (minimal (λ n : Nat => ¬ cond ((prob_while_cut cond body n a s).1))) a
     H.pure (some v)
  else H.pure none

noncomputable def prob_while2 (cond : T → Bool) (body : T → Hurd T) (a : T) (s : BitStream) : Option (Hurd T) :=
  if (∃ n : Nat, ¬ cond ((prob_while_cut cond body n a s).1))
  then some (prob_while_cut cond body (minimal (λ n : Nat => ¬ cond ((prob_while_cut cond body n a s).1))) a)
  else none

def prob_while_terminates (cond : T → Bool) (body : T → Hurd T) : Prop :=
  forall a : T, Prob.volume { s : BitStream | ∃ n : Nat, ¬ cond ((prob_while_cut cond body n a s).1) } = 1

noncomputable def prob_until1 (body : Hurd T) (cond : T → Bool) (s : BitStream) : Hurd (Option T):=
    do let v ← body
       prob_while1 (λ v : T => ¬ cond v) (λ _ : T => body) v s

-- noncomputable def prob_until2 (body : Hurd T) (cond : T → Bool) (s : BitStream) :=
  -- H.bind body (fun v : T => prob_while2 (λ v : T => ¬ cond v) (λ _ : T => body) v s)
    --do let v ← body
    --   prob_while2 (λ v : T => ¬ cond v) (λ _ : T => body) v s
       --match prob_while2 (λ v : T => ¬ cond v) (λ _ : T => body) v s with
       --| none => H.pure none
       --| some v => ...

end Hurd
