import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang
import Mathlib.Data.Set.Basic


namespace MultiBernoulli


open Set

lemma all_lists_eq_all_tails_bool : (univ : Set (List Bool)) = { l | ∃ x xs, l = (x :: xs).tail } := by
  ext l  -- extensionality: sets equal iff same elements
  constructor
  · intro _
    -- show l is in the tail set: pick any Bool x and let xs := l
    use true, l
    rfl
  · rintro ⟨x, xs, h⟩
    -- l = tail of some cons => l is a list => l ∈ univ
    subst h
    let ll := true::l
    have h: ll.tail =l := by rfl
    rw [← h]
    exact mem_univ _
close Set

/- We define the multivariable Bernoulli distrbution (corresponding to n
   independent coin flips) and prove that it normalizes.
   The approach for this is to define a function "explicit_prob" that
   encapsulates the multiplication of probabilities for the independent
   coin flips, and then prove that "MultiBernoulliSample" is equivalent
   to "explicit_prob," in the sense that the two have the same output on any
   input. Given this, the proof of normalization for the multivariate
   Bernoulli distribution reduces to a proof of normalization for the
   explicit_prob function.
-/

lemma tsum_zero (f : List Bool -> ENNReal):
  ∑' (x : List Bool), (if x = [] then 0 else f x) =
  ∑' (x : List Bool), if assm : x ≠ [] then f x else 0 := by simp_all [ite_not]

structure SeedType where
  n : Nat
  d : PNat
  h : n ≤ d
 /- This is just handy shorthand for a rational parameter n/d in [0, 1]-/

/- IGNORE-/
example (b : {b : List Bool // b ≠ []}): b.val.head b.property ∨ ¬ b.val.head b.property := by
  cases b.val.head b.property with
  | true => left; rfl
  | false => right; simp

/- IGNORE -/
def silly: {b : List Bool // b ≠ []} := ⟨[true], by decide⟩

/-IMPORTANT: -/
def bernoulli_mapper: SeedType -> SLang Bool :=
  fun s => SLang.BernoulliSample s.n s.d s.h

lemma bernoulli_mapper_sums_to_1 (s : SeedType): ∑' (b : Bool), bernoulli_mapper s b = 1 := by
  rw[bernoulli_mapper]
  exact SLang.BernoulliSample_normalizes s.n s.d s.h

noncomputable def explicit_prob (hd : SeedType) (tl : List SeedType) (b : List Bool) : ENNReal :=
  match b with
    | [] => 0
    | x :: xs => bernoulli_mapper hd x * (mapM bernoulli_mapper tl) xs

lemma ite_simplifier1 (b : List Bool) (hd : SeedType):
(if assm : b ≠ [] then explicit_prob hd [] b else 0) =
if assm: b ≠ [] then bernoulli_mapper hd (b.head assm) * mapM bernoulli_mapper [] b.tail else 0 := by
  cases b with
  | nil => simp
  | cons x xs => simp_all [explicit_prob, -mapM]

lemma ite_simplifier2 (b : List Bool) (hd : SeedType):
(if h : b = [] then 0 else if b.tail = [] then bernoulli_mapper hd (b.head h) else 0) =
(if assm: b ≠ [] then if b = [b.head assm] then bernoulli_mapper hd (b.head assm) else 0 else 0) := by
  cases b with
  | nil => simp
  | cons x xs => simp

lemma ite_simplifier3 (b : List Bool) (hd : SeedType):
(if assm: b ≠ [] then if b = [b.head assm] then bernoulli_mapper hd (b.head assm) else 0 else 0) =
(if b = [true] then bernoulli_mapper hd true else if b = [false] then bernoulli_mapper hd false else 0) := by
  simp
  cases b with
  | nil => simp
  | cons x xs => simp
                 cases xs with
                 | nil => simp
                          cases x with
                          | true => simp
                          | false => simp
                 | cons => simp

lemma list_bool_length_1 (b : List Bool):
  b.length = 1 ↔ b = [true] ∨ b = [false] := by
   apply Iff.intro
   · intro a
     have h : ∃s : Bool, b = [s] := by
       apply List.length_eq_one.mp
       exact a
     cases h with
     | intro s hs =>
     subst hs
     simp_all only [List.length_singleton, List.cons.injEq, and_true, Bool.eq_true_or_eq_false_self]
   · intro a
     cases a with
     | inl h =>
       subst h
       simp_all only [List.length_singleton]
     | inr h_1 =>
       subst h_1
       simp_all only [List.length_singleton]

lemma sum_simplifier1 (hd : SeedType):
 (if b = [true] then bernoulli_mapper hd true else if b = [false] then bernoulli_mapper hd false else 0)
 = if assm: b.length = 1 then bernoulli_mapper hd (b.head (by aesop)) else 0 := by
  split
  next h =>
    subst h
    simp_all only [List.length_singleton, ↓reduceDIte, List.head_cons]
  next h =>
    split
    next h_1 =>
      subst h_1
      simp_all only [List.cons.injEq, Bool.false_eq_true, and_true, not_false_eq_true, List.length_singleton,
        ↓reduceDIte, List.head_cons]
    next h_1 =>
      split
      next h_2 => apply False.elim
                  have p: ¬ (b = [false] ∨ b = [true]) := by simp_all only [or_self, not_false_eq_true]
                  apply p
                  rw [Or.comm]
                  apply (list_bool_length_1 b).mp
                  exact h_2
      next h_2 => simp_all only

  lemma sum_simplifier2 (hd : SeedType):
   ∑' (b : List Bool), (if b = [true] then bernoulli_mapper hd true else if b = [false] then bernoulli_mapper hd false else 0)
 = ∑' (b : List Bool), if assm: b.length = 1 then bernoulli_mapper hd (b.head (by aesop)) else 0 := by
    conv =>
      enter [1, 1, b]
      rw [sum_simplifier1 hd]

/- EXAMPLE OF WHAT ISN'T WORKING: -/
lemma explicit_prob_sums_to_1 (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), explicit_prob hd tl b = 1 := by
  induction tl with
  | nil => rw [ENNReal.tsum_eq_add_tsum_ite []]
           rw[explicit_prob]
           simp
           convert tsum_zero (explicit_prob hd [])
           apply symm
           conv =>
            enter [1, 1, b]
            rw [ite_simplifier1 b hd]
           convert show (1 + 0 : ENNReal) = 1 from add_zero 1
           simp [-mapM]
           conv =>
            enter [1, 1, b]
            rw [ite_simplifier2 b hd]
            rw [ite_simplifier3 b hd]
           rw[sum_simplifier2 hd]
           rw [←bernoulli_mapper_sums_to_1 hd]
           rw [tsum_bool]
           rw [@AddCommMonoidWithOne.add_comm]
           sorry
           /- FOR ETHAN: At this point I would love to say that
           in the else case, the x ≠ [] and so we can just
           pattern-match on it...but I don't know how to get Lean
           to understand that. -/
  | cons tl_hd tl_tl ih => sorry
/- If we could get the above proof to work, we would be done...-/

/- IGNORE -- after getting stuck with the previous def, I tried to make it
   explicitly recursive, and got stuck...but hopefully we don't need it. -/
 noncomputable def explicit_prob2 (hd : SeedType) (tl : List SeedType) (b : List Bool) : ENNReal :=
  match b with
    | [] => 0
    | x :: xs => bernoulli_mapper hd x *
      match tl with
        | [] => if xs = [] then 1 else 0
        | tl_hd :: tl_tl => explicit_prob2 tl_hd tl_tl xs

lemma bernoulli_mapper_empty (b : List Bool): mapM bernoulli_mapper [] b = if b = [] then 1 else 0 := by
  rw [@List.mapM_nil]
  simp_all only [pure, SLang.pure_apply, ite_eq_right_iff, one_ne_zero, imp_false]
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only

lemma explicit_prob_nonempty (hd : SeedType) (tl : List SeedType) (b : List Bool) (h : b ≠ []):
  explicit_prob hd tl b = bernoulli_mapper hd (b.head h) * (mapM bernoulli_mapper tl b.tail) := by
    rw[explicit_prob]
    cases b with
    | nil => contradiction
    | cons =>
              rename_i head tail
              simp_all only [List.head_cons, List.tail_cons]

lemma explicit_prob_sum_except_empty (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), explicit_prob hd tl b =
  ∑' (b : List Bool), if assm: b ≠ [] then bernoulli_mapper hd (b.head assm) * (mapM bernoulli_mapper tl) b.tail else 0 := by
  unfold explicit_prob
  simp_all only [ne_eq, dite_eq_ite, ite_not]
  sorry

lemma tsum_zero_subtype (f : List Bool -> ENNReal):
  ∑' (b : List Bool), f b = f [] + ∑'(b : {b : List Bool // b ≠ []}), f b.val:= by
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    sorry

lemma explicit_prob2_sums_to_1 (hd : SeedType) (tl : List SeedType):
 ∑' (b : List Bool), explicit_prob2 hd tl b = 1 := by
 induction tl with
 | nil => rw [ENNReal.tsum_eq_add_tsum_ite []]
          rw[explicit_prob2]
          simp
          unfold explicit_prob2
          simp_all only [mul_ite, mul_one, mul_zero]
          rw [tsum_zero]
          sorry
 | cons tl_hd tl_tl ih => rw [ENNReal.tsum_eq_add_tsum_ite []]
                          rw[explicit_prob2]
                          simp
                          sorry


/- IMPORTANT -/
def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM bernoulli_mapper

#check MultiBernoulliSample [SeedType.mk 1 2 (by decide), SeedType.mk 1 2 (by decide)] [true, false]

/- USEFUL LEMMAS: -/
#check @ENNReal.tsum_eq_iSup_sum
#check SLang.BernoulliSample_apply
#check SLang.BernoulliSample_normalizes
#check List.mapM_cons
#check SLang
#check List.mapM_nil
#check tsum_eq_tsum_diff_singleton
#check tsum_ite_eq
#check tsum_eq_single

/- The following theorems might be useful, but are not used in the current proof -/

lemma MultiBernoulli_single_list [LawfulMonad SLang] (hd : SeedType): ∑' (b : List Bool), MultiBernoulliSample [hd] b = 1 := by
  rw [MultiBernoulliSample]
  rw [List.mapM_cons, List.mapM_nil]
  rcases hd with ⟨n, d, h⟩
  simp only [pure, bind]
  simp_all only [SLang.pure_bind, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  rw [@ENNReal.tsum_comm]
  rw [tsum_bool]
  simp_all only [Bool.false_eq_true, ↓reduceIte, tsum_ite_eq]
  rw[←tsum_bool]
  rw[bernoulli_mapper]
  rw [SLang.BernoulliSample_normalizes]

lemma bernoulli_helper [LawfulMonad SLang] (hd : Bool) (hd_1 : SeedType) : bernoulli_mapper hd_1 hd = mapM bernoulli_mapper [hd_1] [hd] := by
  rw [List.mapM_cons, List.mapM_nil]
  rcases hd_1 with ⟨n, d, h⟩
  simp only [pure, bind]
  simp_all only [SLang.pure_bind, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  simp_all only [List.cons.injEq, and_true]
  cases hd with
  | true => simp_all only [Bool.true_eq, tsum_ite_eq]
  | false => simp_all only [Bool.false_eq, tsum_ite_eq, tsum_zero, mul_zero]

/-
lemma bernoulli_mapper_neq_iff (l : List SeedType) (b : List Bool) :
  mapM bernoulli_mapper l [] =
    match l with
    | [] => 1
    | hd :: tl => 0 := by
      cases l with
      | nil =>  simp[-mapM]
      | cons hd tl => simp[-mapM]
                      sorry
-/

/- IMPORTANT: Here we prove that explicit_prob is the same as MultiBernoulliSample-/
lemma multi_bernoulli_explicit [LawfulMonad SLang] (hd : SeedType) (tl : List SeedType) (b : List Bool):
  mapM bernoulli_mapper (hd :: tl) b = explicit_prob hd tl b := by
  unfold explicit_prob
  rw[List.mapM_cons]
  simp_all only [bind, pure, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  split
  next b => simp_all only [↓reduceIte, tsum_zero, mul_zero]
            simp
  next b x xs =>
    simp_all only [List.cons.injEq]
    rw[tsum_bool]
    cases x with
    | false => simp[-mapM]
               rw[tsum_eq_single xs]
               simp_all
               intro b' a
               simp_all only [ne_eq, mapM, ite_eq_right_iff]
               intro a_1
               subst a_1
               simp_all only [not_true_eq_false]
    | true =>  simp[-mapM]
               rw[tsum_eq_single xs]
               simp_all
               intro b' a
               simp_all only [ne_eq, mapM, ite_eq_right_iff]
               intro a_1
               subst a_1
               simp_all only [not_true_eq_false]

lemma multi_bernoulli_explicit_sum [LawfulMonad SLang] (hd : SeedType) (tl : List SeedType):
 ∑' (b : List Bool), mapM bernoulli_mapper (hd :: tl) b = ∑' (b : List Bool), explicit_prob hd tl b := by
  simp_all [multi_bernoulli_explicit, -mapM]

/- noncomputable def unsimplified_expression (hd : SeedType) (tl : List SeedType) (x : List Bool): ENNReal :=
  if x = [] then (0 : ENNReal)
      else
        match x with
        | [] => (0 : ENNReal)
        | x :: xs => bernoulli_mapper hd x * mapM bernoulli_mapper tl xs -/

/- lemma simplify_unsimplified (hd : SeedType) (tl : List SeedType) (x : List Bool) (h : x ≠ []):
   unsimplified_expression hd tl x =
   bernoulli_mapper hd (x.head h) * mapM bernoulli_mapper tl x.tail := by
    unfold unsimplified_expression
    simp_all only [↓reduceIte, mapM]
    split
    next b =>
      simp_all only [List.tail_nil, zero_eq_mul]
      apply Or.inr
      simp_all only [ne_eq, not_true_eq_false]
    next b x xs => simp_all only [List.head_cons, List.tail_cons] -/

/- lemma list_bool_tsum_rw {T : Type} [DecidableEq T] [AddCommMonoid T] [TopologicalSpace T] (f : List Bool -> T):
  ∑' (b : List Bool), f b = f [] + ∑' (b : {b : List Bool // b ≠ []}), f b := by
  sorry -/

lemma tsum_equal_comp {α β: Type} [AddCommMonoid β] [TopologicalSpace β] (f g : α -> β) (h: ∀i : α, f i = g i ):
   ∑' (i : α), f i = ∑' (i : α), g i := by simp_all

/- lemma multibernoulli_of_zero [LawfulMonad SLang] (seed: SeedType):
  MultiBernoulliSample [seed] [] = 0 := by
    rw [MultiBernoulliSample]
    rw [List.mapM_cons]
    simp_all only [bind, pure, SLang.bind_apply, SLang.pure_apply, ↓reduceIte, mul_zero, tsum_zero] -/

/- lemma MultiBernoulli_independence_single [LawfulMonad SLang] (hd : SeedType) (tl : List SeedType) (b : List Bool):
  MultiBernoulliSample (hd :: tl) b = if assm: b ≠ [] then MultiBernoulliSample [hd] [b.head (by assumption)] * MultiBernoulliSample tl (b.tail) else 0 := by
    unfold MultiBernoulliSample
    cases b with
    | nil => simp [-mapM]
    | cons hd tl =>
    rename_i inst hd_1 tl_1
    simp_all only [ne_eq, not_false_eq_true, ↓reduceDIte, List.head_cons, List.tail_cons]
    sorry -/

/- lemma MultiBernoulli_independence [LawfulMonad SLang] (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), MultiBernoulliSample (hd :: tl) b =
  ∑' (b : List Bool), if assm: b ≠ [] then MultiBernoulliSample [hd] [b.head (by assumption)] * MultiBernoulliSample tl (b.tail) else 0 := by
    unfold MultiBernoulliSample
    rw [multi_bernoulli_explicit_sum]
    unfold explicit_prob
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    simp_all only [zero_add]
    rw[tsum_equal_comp]
    intro b
    cases b with
    | nil => simp [-mapM]
    | cons hd tl =>
             rename_i inst hd_1 tl_1
             simp_all only [↓reduceIte, ne_eq, not_false_eq_true, ↓reduceDIte, List.head_cons, List.tail_cons]
             sorry -/

/- This can be proven by showing that explicit_prob normalizes. -/

lemma simplifier1 (a : List Bool) (b : Bool):
(∑' (a_1 : List Bool), if a = b :: a_1 then mapM bernoulli_mapper tl a_1 else 0) =
(if a.head? = b then mapM bernoulli_mapper tl a.tail else 0) := by
  cases a with
  | nil => simp
  | cons ah atl =>
    simp [-mapM]
    split
    next h =>
      subst h
      simp_all only [true_and]
      rw [tsum_eq_single]
      --simp_all only [mapM]
      split
      rename_i h
      on_goal 2 => rename_i h
      apply Eq.refl
      simp_all only [not_true_eq_false]
      intro b' a
      simp_all only [ne_eq, mapM, ite_eq_right_iff]
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]
    next h => simp_all only [false_and, ↓reduceIte, _root_.tsum_zero]




lemma simplifierNOTNEEDED (a : List Bool):
(if a = [] then 0 else bernoulli_mapper hd false * mapM bernoulli_mapper tl a.tail) +
  (if a = [] then 0 else bernoulli_mapper hd true * mapM bernoulli_mapper tl a.tail)
= (if a = [] then 0 else bernoulli_mapper hd false * mapM bernoulli_mapper tl a.tail +
  bernoulli_mapper hd true * mapM bernoulli_mapper tl a.tail) := by aesop

lemma simplifier2 (hd : SeedType) (tl : List SeedType) (b : Bool):
(∑' (a : List Bool), bernoulli_mapper hd b * if a.head? = some b then mapM bernoulli_mapper tl a.tail else 0) =
 ∑' (a : List Bool), bernoulli_mapper hd b * mapM bernoulli_mapper tl a := by sorry

lemma ennreal_mul_eq (a b c : ENNReal): a = b -> c * a = c * b := by
  intro h
  rw[h]

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

lemma tsum_func_zero_simp (f : List Bool -> ENNReal) (h : f [] = 0):
  ∑' (x : List Bool), f x = (∑'(x : List Bool), if x = [] then 0 else f x) := by
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    simp [h]
    apply tsum_equal_comp
    intro i
    aesop

lemma MultiBernoulliSample_normalizes [LawfulMonad SLang] (seeds : List SeedType) :
  ∑' (b: List Bool), MultiBernoulliSample seeds b = 1 := by
    rw [MultiBernoulliSample]
    induction seeds with
    | nil => rw [@List.mapM_nil]
             simp[pure]
             rw [ENNReal.tsum_eq_add_tsum_ite []]
             simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
             simp
    | cons hd tl ih =>
      simp [List.mapM_cons, -mapM]
       /- rw [@ENNReal.tsum_comm]
      rw [tsum_bool]
      rw [← @ENNReal.tsum_add] -/
      conv =>
        enter [1, 1, b, 1, a]
        simp [-mapM]
        rw [simplifier1]
      /- rewrite as a double sum, the first sum being over possible a.heads, and the second
         some being over all list Bools, with the conditional now being on the Boolean
         in the first sum. Afterwards, it should be straightforward to use the inductive hypothesis -/
      rw [@ENNReal.tsum_comm]
      conv =>
        enter [1, 1, b]
        rw [simplifier2]
      rw [@ENNReal.tsum_comm]
      rw?
      sorry


      sorry

/- The rest of this file can be ignored. It states that the push-forward
   of a probability measure is a probability measure, which we don't
   need for now. -/

noncomputable def push_forward {T S: Type} [DecidableEq S] (p : SLang T) (f : T -> S) : SLang S :=
  fun s => ∑' (t : T), if f t = s then p t else 0

lemma push_forward_prob_is_prob {T S : Type} [DecidableEq S] (p : SLang T) (f : T -> S) (h : ∑' (t : T), p t = 1) :
  ∑' (s : S), (push_forward p f) s = 1 := by
    simp [push_forward]
    rw [@ENNReal.tsum_comm]
    have h1: ∀b : T, ∑' (a : S), (if f b = a then p b else 0 : ENNReal) = p b := by
      intro b
      rw [tsum_eq_single (f b)]
      simp
      intro b' a
      simp_all only [ne_eq, ite_eq_right_iff]
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]
    simp_all

lemma explicit_prob_eq_prob2 [LawfulMonad SLang] (hd : SeedType) (tl : List SeedType) (b : List Bool) :
  explicit_prob hd tl b = explicit_prob2 hd tl b := by
  induction b generalizing hd with
  | nil => unfold explicit_prob explicit_prob2
           simp_all only [mapM, bernoulli_mapper, pure, SLang.pure_apply, zero_mul]
  | cons n ns ih => simp [explicit_prob, -mapM]
                    unfold explicit_prob2
                    split
                    next tl =>
                      simp_all only [mul_ite, mul_one, mul_zero]
                      split
                      next h =>
                        subst h
                        rw [List.mapM_nil]
                        simp [pure]
                      next h =>
                        simp_all only [mul_eq_zero]
                        apply Or.inr
                        rw [List.mapM_nil]
                        simp [pure]
                        exact h
                    next tl tl_hd tl_tl =>
                      simp[explicit_prob, -mapM] at ih
                      split at ih
                      next b => simp [explicit_prob2, -mapM]
                      next b x xs => apply ennreal_mul_eq
                                     unfold explicit_prob2
                                     rw [List.mapM_cons]
                                     simp [-mapM]
                                     rw[tsum_bool]
                                     cases tl_tl with
                                     | nil => simp only [mul_ite, mul_one, mul_zero]
                                              rename_i inst
                                              split
                                              next h =>
                                                subst h
                                                simp_all only [↓reduceIte, _root_.tsum_zero, mul_zero]
                                                cases x with
                                                | true =>
                                                simp_all only [Bool.true_eq_false, false_and, ↓reduceIte,
                                                  _root_.tsum_zero, mul_zero, true_and, zero_add]
                                                simp [tsum_eq_single, -mapM]
                                                simp_all [tsum_ite_eq]
                                                rw [tsum_eq_single []]
                                                simp
                                                intro b hb
                                                simp
                                                exact id (Ne.symm hb)
                                                | false =>
                                                simp_all only [Bool.true_eq_false, false_and, ↓reduceIte,
                                                  _root_.tsum_zero, mul_zero, true_and, zero_add]
                                                simp [tsum_eq_single, -mapM]
                                                simp_all [tsum_ite_eq]
                                                rw [tsum_eq_single []]
                                                simp
                                                intro b hb
                                                simp
                                                exact id (Ne.symm hb)
                                              next
                                                h =>
                                                simp_all only [add_eq_zero, mul_eq_zero, ENNReal.tsum_eq_zero,
                                                  ite_eq_right_iff, and_imp, forall_apply_eq_imp_iff]
                                                apply And.intro
                                                · apply Or.inr
                                                  intro hx
                                                  rw [List.mapM_nil]
                                                  simp [pure]
                                                  exact h
                                                · apply Or.inr
                                                  intro hx
                                                  rw [List.mapM_nil]
                                                  simp [pure]
                                                  exact h
                                     | cons =>





                                     sorry











end MultiBernoulli
