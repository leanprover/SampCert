import SampCert

open SLang

/- This proves that the push-forward of a probability measure is a probability measure.
We use this when defining UniformSample', i.e., UniformSample as an SLang (Fin n). -/

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
