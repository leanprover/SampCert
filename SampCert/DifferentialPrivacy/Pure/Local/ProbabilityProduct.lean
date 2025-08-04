import SampCert.DifferentialPrivacy.Pure.Local.ENNRealLemmasSuite

namespace SLang

open ENNRealLemmas
/- Helper lemma about mapM to prove "prod_of_ind_prob"-/
lemma mapM_dist_cons {β : Type} [LawfulMonad SLang] [DecidableEq β] (f: T → SLang β) (b: β)(c: List β)(hd: T)(tl: List T):
mapM f (hd :: tl) (b :: c) = f hd b * mapM f tl c := by
  rw[List.mapM_cons]
  simp[-mapM]
  conv =>
    enter [1, 1, a, 2]
    simp[-mapM]
    rw [simplifier_3]
  rw [tsum_eq_single b]
  aesop
  aesop

/- First step of the DP Proof: using indepenendence to rewrite the total probability
   as a product of probabilities. -/
lemma prod_of_ind_prob (β : Type) [LawfulMonad SLang] [DecidableEq β] (f : T -> SLang β) (a : List β) (l : List T) (k : l.length = a.length) :
  mapM f l a = (∏' (i : Fin l.length), f (l.get i) (a.get (Fin.cast k i))) := by
  induction l generalizing a with
  | nil =>
    simp[-mapM]
    rw[List.length_nil] at k
    symm at k
    apply List.eq_nil_of_length_eq_zero at k
    rw[k]
  | cons hd tl ih =>
    cases a with
    | nil =>
      simp at k
    | cons b c =>
      rw [mapM_dist_cons]
      rw [ih c]
      rw [@tprod_fintype]
      rw [@tprod_fintype]
      simp
      rw[Fin.prod_univ_succ]
      simp at k
      apply Eq.refl
      aesop

end SLang
