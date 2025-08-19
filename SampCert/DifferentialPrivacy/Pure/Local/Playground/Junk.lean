import SampCert

/-
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

/- /- Version of the prod_of_ind_prob lemma for the PMF instantiation of RRSample. -/
theorem RRSample_prod_of_ind_prob_PMF(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- Proof of DP for Randomized Response. We use the reduction lemma from a different file. -/
theorem RRSample_is_DP (query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den) :
DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den))) := by
apply singleton_to_event_update
intros l₁ l₂ h_adj x
cases xlen1 : l₁.length == x.length with
| true =>
          rw[RRSample_prod_of_ind_prob_PMF query num den h x l₁ (by aesop)]
          rw[RRSample_prod_of_ind_prob_PMF query num den h x l₂
          (by rw[←UpdateNeighbour_length h_adj]
              simp at xlen1
              exact xlen1)]
          cases h_adj with
          | Update hl₁ hl₂ =>
                        rename_i a n b m
                        have hlen: l₁.length = l₂.length := by aesop
                        have xlen2 : l₂.length = x.length := by aesop
                        simp
                        have xlen3 : l₁.length = x.length := by aesop
                        rw[reduction_final l₁ l₂ a b n m x (RRSingleSample query num den h ) hl₁ hl₂ xlen3 xlen2]
                        have i1: a.length < x.length := by
                          rw[←xlen3]
                          subst hl₁ hl₂
                          simp_all only [List.append_assoc, List.singleton_append, List.length_append,
                            List.length_cons, beq_iff_eq]
                          rw[←xlen1]
                          rw [@Nat.lt_add_right_iff_pos]
                          simp
                        {calc
                        RRSingleSample query num den h (l₁[a.length]'(by aesop)) (x[a.length]'(by aesop))
                        / RRSingleSample query num den h (l₂[a.length]'(by aesop)) (x[a.length]'(by aesop)) ≤ (den + 2 * num) / (den - 2 * num) := by apply final_bound
                        _ ≤ ENNReal.ofReal (Real.exp (Real.log ((1/2 + num/den) / (1/2 - num/den)))) := by
                          apply final_coercion
                          exact h
                        _ ≤   ENNReal.ofReal (Real.exp (Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by aesop
                        }
                        {intro i
                         apply RRSingleSample_non_zero query num den h}
                        {apply RRSingleSample_finite query num den h}
| false => simp at xlen1
           rw [←Ne.eq_def] at xlen1
           have numerator_zero: RRSample_PMF query num den h l₁ x = 0 := by
            rw [RRSamplePMF_diff_lengths]
            exact xlen1
           rw [numerator_zero]
           rw [@ENNReal.zero_div]
           simp

/- A different perspective-/ -/

/- /-/- This allows us to use prob_ind_prob in the RAPPOR DP proof -/
lemma RAPPOR_prob_of_ind_prob_PMF {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) (a: List (List Bool)) (k : v.length = a.length) :
  RAPPORSample_PMF n query num den h v a = (∏'(i: Fin v.length), RAPPORSingleSample n query num den h (v.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- Uses the one-hot-encoding lemmas to rewrite a quotient of RRSinglePushForward applications into an if-then-else statement -/
lemma reduction_helper1 {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length) (h_users: query u ≠ query v) (i : Fin (one_hot n query u).length):
  RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] /
  RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val] =
  if query v = (finCongr (by aesop) i) then RRSinglePushForward num den h (one_hot n query v)[query v] (b[query v]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[query v] (b[query v]'(by aesop))
  else if query u = (finCongr (by aesop) i) then RRSinglePushForward num den h (one_hot n query v)[query u] (b[query u]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[query u] (b[query u]'(by aesop))
  else 1 := by
  cases hi : (finCongr (by aesop) i) == query v with
  | true => simp at hi
            have h1: i.val = (query v).val := by
              rw [← hi]
              simp
            aesop
  | false => simp at hi
             cases hi2: (finCongr (by aesop) i) == query u with
             | true => simp at hi2
                       have h1: i.val = (query u).val := by
                          rw [← hi2]
                          simp
                       simp [h1, -one_hot]
                       simp_all only [not_false_eq_true, List.getElem_ofFn, Fin.eta, decide_True,
                         decide_False, ↓reduceIte]
                       split
                       next h_1 =>
                         simp_all only [decide_True]
                       next h_1 => simp_all only [decide_False]
             | false => simp at hi2
                        simp_all only [List.getElem_ofFn, finCongr_apply, Fin.getElem_fin, Fin.coe_cast,
                          Fin.eta]
                        split
                        next h_1 => simp_all only [not_true_eq_false]
                        next h_1 =>
                          split
                          next h_2 => simp_all only [not_true_eq_false]
                          next h_2 =>
                          have h1: (one_hot n query v)[i.val]'(by omega) = (one_hot n query u)[i.val]'(by omega) :=
                            by convert one_hot_different_answer_ex_two_contrp' n query v u (finCongr (by aesop) i)
                               aesop
                          rw [h1]
                          rw [ENNReal.div_self]
                          apply RRSinglePushForward_non_zero
                          apply RRSinglePushForward_finite

/- Rewrites the if-then-else statement from above into a simpler form, with most terms cancelled. -/
lemma reduction_helper2 {T : Type} (n : Nat) (query: T -> Fin n) (f : Bool -> SLang Bool) (v u : T) (b : List Bool) (h_users: query u ≠ query v)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
  (∏ i : Fin (one_hot n query u).length,
    if query v = (finCongr (by aesop) i) then f (one_hot n query v)[query v] (b[query v]'(by aesop)) / f (one_hot n query u)[query v] (b[query v]'(by aesop))
    else if query u = (finCongr (by aesop) i) then f (one_hot n query v)[query u] (b[query u]'(by aesop)) / f (one_hot n query u)[query u] (b[query u]'(by aesop))
    else 1) =
  f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
  * f (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop))
   := by
    simp_all only [finCongr_apply, Fin.getElem_fin, Fin.coe_cast, List.getElem_ofFn, Fin.eta]
    have _ (g : Fin b.length -> ENNReal) : ∏ i : Fin b.length, g i = ∏ (i ∈ Finset.univ), g i := by aesop
    conv =>
      enter [1]
      rw [@Finset.prod_ite]
      simp [-one_hot]
      rw [@Finset.prod_ite]
      simp [-one_hot]
    simp_all only [finCongr_apply, implies_true, List.getElem_ofFn, Fin.eta, decide_True]
    have hblen : b.length = n := by aesop
    have h5 (k : T): Finset.filter (fun x => query k = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)) = {finCongr (by aesop) (query k)} := by aesop
    have h6: (Finset.filter (fun x => query u = Fin.cast (by aesop) x) (Finset.filter (fun x => ¬query v = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)))).card = 1 := by
        rw [@Finset.card_eq_one]
        use (finCongr (by aesop) (query u))
        aesop
    have h8: ∏ x ∈ Finset.filter (fun x => query v = Fin.cast (by aesop) x) (Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
             = f (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / f (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop)) := by
              subst hblen
              simp_all only [List.getElem_ofFn, Fin.eta, Finset.prod_const]
              conv =>
                enter [1, 2]
                simp
              simp
    have h9: ∏ x ∈ Finset.filter (fun x => query u = Fin.cast (by aesop) x) (Finset.filter (fun x => ¬query v = Fin.cast (by aesop) x) Finset.univ : Finset (Fin (one_hot n query u).length)),
             f (one_hot n query v)[(query u).val] (b[(query u).val]'(by
             simp_all only [List.getElem_ofFn, Fin.eta, decide_True, decide_False, Fin.is_lt])) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by
             simp_all only [one_hot, List.getElem_ofFn, Fin.eta, decide_True, decide_False, Fin.is_lt]))
             = f (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / f (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop)) := by
             simp_all only [List.getElem_ofFn, Fin.eta, decide_True, Finset.prod_const]
             simp
    rw [h8]
    rw [h9]
    rw [@mul_div]

/- Cancellation of terms in the DP proof by using the above two lemmas.-/
lemma single_DP_reduction {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v u : T) (b : List Bool) (h_users: query u ≠ query v)
 (ohu_len : (one_hot n query u).length = b.length) (onhv_len : (one_hot n query v).length = b.length):
∏ i : Fin (one_hot n query u).length, RRSinglePushForward num den h (one_hot n query v)[i.val] b[i.val] / RRSinglePushForward num den h (one_hot n query u)[i.val] b[i.val]
 = RRSinglePushForward num den h (one_hot n query v)[(query v).val] (b[(query v).val]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[(query v).val] (b[(query v).val]'(by aesop))
 * RRSinglePushForward num den h (one_hot n query v)[(query u).val] (b[(query u).val]'(by aesop)) / RRSinglePushForward num den h (one_hot n query u)[(query u).val] (b[(query u).val]'(by aesop))
 := by
 conv =>
  enter [1, 2, i]
  rw [reduction_helper1 n query num den h v u b ohu_len onhv_len h_users i]
 rw [reduction_helper2 _ _ _ _ _ _ h_users]
 simp_all only [mul_one]
 exact onhv_len
-/

/-
/- This extends the previous DP lemma to a dataset of arbitrary size -/
lemma RAPPORSample_is_DP {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (b : List Bool):
  DP_withUpdateNeighbour (RAPPORSample_PMF n query num den h) (2 * Real.log ((2⁻¹ + num/den) / (2⁻¹ - num/den)))
   := by
      apply singleton_to_event_update
      intros l₁ l₂ h_adj x
      cases xlen1 : l₁.length == x.length with
      | true => simp at xlen1
                have xlen2: l₂.length = x.length := by
                  rw [←xlen1]
                  rw[←UpdateNeighbour_length h_adj]
                rw[RAPPOR_prob_of_ind_prob_PMF n query num den h l₁ x xlen1]
                rw[RAPPOR_prob_of_ind_prob_PMF n query num den h l₂ x xlen2]
                cases h_adj with
                | Update hl₁ hl₂ =>
                  rename_i a y c z
                  simp
                  cases x_indices: (∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by apply valid_index4 _ hl₂; apply xlen2)).length = n) == true with
                  | true =>
                  simp at x_indices
                  have valid_index5: a.length < l₁.length := by
                    rw [hl₁]
                    rw [@List.length_append]
                    simp_all only [List.append_assoc, List.singleton_append, List.length_append, List.length_cons,
                      List.length_singleton]
                    linarith
                  have valid_index6: a.length < x.length := by
                    rw [←xlen1]
                    exact valid_index5
                  have valid_index7: a.length < l₂.length := by
                    rw [xlen2]
                    exact valid_index6
                  rw [reduction_final_RAP n l₁ l₂ x (fun _ => RAPPORSingleSample n query num den h ) hl₁ hl₂ xlen1 _ xlen2]
                  { calc
                    RAPPORSingleSample n query num den h (l₁[a.length]'(valid_index5)) (x[a.length]'(valid_index6)) /
                    RAPPORSingleSample n query num den h (l₂[a.length]'(valid_index7)) (x[a.length]'(valid_index6)) ≤
                    ((2⁻¹ + num / den) / (2⁻¹ - num / den)) ^ 2 := by apply RAPPORSingle_DP n query num den h
                    _ = ENNReal.ofReal (Real.exp (2 * Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by rw[←arith_2 num den h]
                  }
                  {
                    intro k bo hbo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_non_zero
                    aesop
                  }
                  { intro k bo
                    rw [RAPPORSingleSample]
                    apply RRSamplePushForward_finite
                  }
                  {apply x_indices}
                  | false =>
                  simp at x_indices
                  cases x_indices with
                  | intro i hi =>
                  have numerator_zero: (∏' (i : Fin l₁.length), RAPPORSingleSample n query num den h l₁[i.val] x[i.val]) = 0 := by
                    rw [@tprod_fintype]
                    rw[Finset.prod_eq_zero_iff]
                    norm_num
                    have hl1len:l₁.length > 0 := by
                     rw[hl₁]
                     rw [@List.length_append]
                     aesop
                    use (Fin.ofNat' i.val (hl1len))
                    apply RAPPORSingleSample_diff_lengths n query num den h
                    simp
                    have h_coe: i.val % l₁.length = i.val := by
                     rw [Nat.mod_eq]
                     have hival: i.val < l₁.length := by
                      rw [xlen1]
                      apply valid_index4 _ hl₂
                      exact xlen2
                     aesop
                    conv =>
                     enter[1, 2, 1, 2]
                     rw[h_coe]
                    aesop
                  rw [numerator_zero]
                  rw [@ENNReal.zero_div]
                  simp
      | false => simp at xlen1
                 rw [←Ne.eq_def] at xlen1
                 have numerator_zero: RAPPORSample_PMF n query num den h l₁ x = 0 := RAPPORSample_diff_lengths n query num den h l₁ x xlen1
                 rw [numerator_zero]
                 rw [@ENNReal.zero_div]
                 simp

/- A different perspective -/
-/ -/

/-
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.DPProof

open RandomizedResponse

/- Step 2 of the DP Proof over a dataset: cancellation of probabilities in the numerator and denominator. -/

lemma fin_prod_cast_RAP {n m : ℕ} (h : n = m)(f : Fin n → ENNReal) :
  ∏' i : Fin n, f i = ∏' i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  simp

lemma conversion_RAP {β: Type}(l: List T) (x: List β)(h1: l = a++[n]++b)(hl : l.length ≥ 1)(hx: l.length = x.length)(f: T → SLang β): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) := by
  rw [fin_prod_cast (by rw [← Nat.sub_add_cancel hl])]
  simp

lemma fin_conv_helper (l₂ : List T) (hl₂: l₂ = a++[m]++b): l₂.length - 1 + 1 = l₂.length := by --this is useful later
                  rw [Nat.sub_add_cancel]
                  rw [@Nat.succ_le_iff]
                  rw [hl₂]
                  rw [@List.length_append]
                  aesop
lemma valid_index4 (l₂ : List T) (hl₂ : l₂ = a++[m]++b)(x : List (List Bool)) (i : Fin (l₂.length - 1 + 1)) (xlen2 : l₂.length = x.length): i.val < x.length := by
  conv =>
    enter [2]
    rw [←xlen2]
    rw [←fin_conv_helper _ hl₂]
  exact i.2

lemma reduction2_RAP (n : Nat) (l₁ l₂: List T)(x: List (List Bool)) (f: Nat -> T → SLang (List Bool))(h1: l₁ = a++[l]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length) (hx2 : ∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by apply valid_index4; apply h2; aesop)).length = n) (hy: l₂.length = x.length) (nonzero: ∀(k: T) (bo: (List Bool)), bo.length = n -> f n k bo ≠ 0) (noninf: ∀(k: T) (bo: (List Bool)), f n k bo ≠ ⊤):(∏' (i : Fin ((l₁.length-1)+1)), f n (l₁[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) /
    (∏' (i : Fin ((l₂.length-1)+1)), f n (l₂[i.val]'(valid_index2 h2 i)) (x[i.val]'(valid_index3 h2 hy i)))  = f n (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) / f n (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) := by
    rw[tprod_fintype]
    rw[tprod_fintype]
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₁.length-1)+1)) => f n (l₁[b.val]'(valid_index2 h1 b)) (x[b.val]'(valid_index3 h1 hx b))) a.length]
    have ind: a.length < x.length := by
      rw[← hx]
      rw[h1]
      simp
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₂.length-1)+1)) => f n (l₂[b.val]'(valid_index2 h2 b)) (x[b.val]'(valid_index3 h2 hy b))) a.length]
    have helper: l₁.length - 1 = l₂.length - 1 := by aesop
    have hlp: (∏ i : Fin (l₁.length - 1), f n l₁[(Fin.succAbove a.length i).val] x[↑(Fin.succAbove a.length i).val]) = ∏ i : Fin (l₂.length - 1), f n l₂[(Fin.succAbove a.length i).val] x[(Fin.succAbove a.length i).val] := by
      apply Fintype.prod_equiv (Equiv.cast (congr_arg Fin helper))
      simp[succHelp l₁ l₂ h1 h2]
      intro i
      congr
      rw [← propext cast_eq_iff_heq]
      rw [← propext cast_eq_iff_heq]
    rw[hlp]
    rw[ENNReal.mul_div_mul_right]
    simp

    simp[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
    simp[mod_helper (a.length) (l₂.length) (by rw[h2];simp;linarith) (by rw[h2]; simp)]

    rw[Finset.prod_ne_zero_iff]
    intro i
    aesop
    rw[← lt_top_iff_ne_top]
    apply ENNReal.prod_lt_top
    intro i
    simp[noninf]

theorem reduction_final_RAP (n : Nat) (l₁ l₂: List T)(x: List (List Bool)) (f: Nat -> T → SLang (List Bool)) (h1: l₁ = a++[l]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length) (hx2 : ∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by apply valid_index4; apply h2; aesop)).length = n) (hy: l₂.length = x.length)(nonzero: ∀(k: T) (bo: (List Bool)), bo.length = n -> f n k bo ≠ 0)(noninf: ∀(k: T) (bo: (List Bool)), f n k bo ≠ ⊤):(∏' (i : Fin (l₁.length)), f n (l₁[i.val]'(by simp)) (x[i.val]'(by rw[← hx]; simp))) /
    (∏' (i : Fin (l₂.length)), f n (l₂[i.val]'(by simp)) (x[i.val]'(by rw[← hy];simp)))  = f n (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) / f n (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) := by
    have hl2: l₂.length ≥ 1 := by rw[h2];simp; linarith
    have hl1: l₁.length ≥ 1 := by rw[h1];simp; linarith
    rw[conversion_RAP l₂ x h2 hl2 hy (f n)]
    rw[conversion_RAP l₁ x h1 hl1 hx (f n)]
    rw [reduction2_RAP n l₁ l₂ x f h1 h2 hx hx2 hy nonzero noninf]

open Finset
open scoped BigOperators

-/
-/ 
