import SampCert

open MultiBernoulli

/- These is stuff that might be helpful for understanding
   how to deal with some specific Lean issues, mainly
   to do with manipulating tsums and List.mapM, but isn't
   actually used for anything at this point. -/

/- WORKING WITH SUBTYPES: -/
example (b : {b : List Bool // b ≠ []}): b.val.head b.property ∨ ¬ b.val.head b.property := by
  cases b.val.head b.property with
  | true => left; rfl
  | false => right; simp

def silly: {b : List Bool // b ≠ []} := ⟨[true], by decide⟩

/- SIMPLIFICATION LEMMAS FOR IF-THEN-ELSE STATEMENTS: -/
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

lemma all_list_eq_all_true_tails (b: Bool):(univ : Set (List Bool)) = { l | ∃ xs, l = (b :: xs).tail } := by
  ext l
  constructor
  intro _
  simp_all only [mem_univ, List.tail_cons, exists_eq', setOf_true]
  intro _
  simp_all only [List.tail_cons, exists_eq', setOf_true, mem_univ]
