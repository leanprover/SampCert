/-
Copyright (c) 2026 Michael Shoemate.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.Polynomials

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Counting and permutation-combinatorics lemmas for the paper-style proof.

Reading guide:
- `latestIn` and `beforeSet` encode the paper's "items before `r` in a permutation" events;
- the middle of the file proves the exact uniform coefficient `1 / (|t| + 1)`;
- the later lemmas package those coefficients for the closed-form PMF bridge.
-/

/-! ### Part I: latest-in combinatorics

This first block proves a symmetry fact about uniform random permutations:
for a fixed nonempty finite set `s`, every element of `s` is equally likely to
be the latest element of `s` in the permutation.

The paper uses this symmetry implicitly to obtain the coefficient
`1 / (|t| + 1)` that appears in the closed-form PMF.
-/

def latestIn {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ)) (r : Fin n.succ) : Prop :=
  r ∈ s ∧ ∀ i ∈ s, σ.symm i ≤ σ.symm r

@[simp]
theorem swap_trans_symm_apply {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r t i : Fin n.succ) :
    (σ.trans (Equiv.swap r t)).symm i = σ.symm ((Equiv.swap r t) i) := by
  simp [Equiv.symm_trans_apply]

theorem latestIn_unique {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ))
    {r t : Fin n.succ} (hr : latestIn σ s r) (ht : latestIn σ s t) :
    r = t := by
  rcases hr with ⟨hrmem, hrlt⟩
  rcases ht with ⟨htmem, htlt⟩
  apply σ.symm.injective
  exact le_antisymm (htlt r hrmem) (hrlt t htmem)

theorem exists_latestIn {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ)) (hs : s.Nonempty) :
    ∃ r, latestIn σ s r := by
  obtain ⟨r, hrmem, hrmax⟩ := Finset.exists_max_image s σ.symm hs
  refine ⟨r, hrmem, ?_⟩
  intro i hi
  exact hrmax i hi

theorem existsUnique_latestIn {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ)) (hs : s.Nonempty) :
    ∃! r, latestIn σ s r := by
  obtain ⟨r, hr⟩ := exists_latestIn σ s hs
  refine ⟨r, hr, ?_⟩
  intro t ht
  exact latestIn_unique σ s ht hr

theorem latestIn_swap {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ))
    (r t : Fin n.succ) (hr : r ∈ s) (ht : t ∈ s) :
    latestIn σ s r → latestIn (σ.trans (Equiv.swap r t)) s t := by
  by_cases hrt : r = t
  · subst hrt
    simp [latestIn]
  · intro h
    rcases h with ⟨_, hlt⟩
    refine ⟨ht, ?_⟩
    intro i hi
    have hmem : (Equiv.swap r t) i ∈ s := by
      by_cases hir : i = r
      · subst hir
        simpa [Equiv.swap_apply_def, hrt] using ht
      · by_cases hit : i = t
        · subst hit
          simpa [Equiv.swap_apply_def, hrt] using hr
        · simpa [Equiv.swap_apply_def, hir, hit] using hi
    have hbound : σ.symm ((Equiv.swap r t) i) ≤ σ.symm ((Equiv.swap r t) t) := by
      simpa [Equiv.swap_apply_def, hrt] using hlt ((Equiv.swap r t) i) hmem
    simpa [swap_trans_symm_apply, Equiv.swap_apply_def, hrt] using hbound

theorem latestIn_swap_iff {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (s : Finset (Fin n.succ))
    (r t : Fin n.succ) (hr : r ∈ s) (ht : t ∈ s) :
    latestIn σ s r ↔ latestIn (σ.trans (Equiv.swap r t)) s t := by
  constructor
  · exact latestIn_swap σ s r t hr ht
  · intro h
    have h' :
        latestIn ((σ.trans (Equiv.swap r t)).trans (Equiv.swap t r)) s r :=
      latestIn_swap (σ.trans (Equiv.swap r t)) s t r ht hr h
    have hcomp : (σ.trans (Equiv.swap r t)).trans (Equiv.swap t r) = σ := by
      ext x
      by_cases hsxr : σ x = r
      · by_cases hsxt : σ x = t
        · have : r = t := hsxr.symm.trans hsxt
          subst this
          simp [Equiv.trans_apply, Equiv.swap_apply_def, hsxr]
        · simp [Equiv.trans_apply, Equiv.swap_apply_def, hsxr, hsxt]
      · by_cases hsxt : σ x = t
        · simp [Equiv.trans_apply, Equiv.swap_apply_def, hsxr, hsxt]
        · simp [Equiv.trans_apply, Equiv.swap_apply_def, hsxr, hsxt]
    simpa [hcomp] using h'

theorem card_filter_latestIn_eq {n : CandidateCount}
    (s : Finset (Fin n.succ)) (_hs : s.Nonempty)
    {r t : Fin n.succ} (hr : r ∈ s) (ht : t ∈ s) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s t).card := by
  classical
  refine Finset.card_nbij'
    (fun σ => σ.trans (Equiv.swap r t))
    (fun σ => σ.trans (Equiv.swap t r))
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simpa [Finset.mem_filter] using
      (latestIn_swap_iff σ s r t hr ht).mp (by simpa [Finset.mem_filter] using hσ)
  · intro σ hσ
    simpa [Finset.mem_filter] using
      (latestIn_swap_iff σ s t r ht hr).mp (by simpa [Finset.mem_filter] using hσ)
  · intro σ _hσ
    ext x
    simp [Equiv.trans_apply]
    by_cases hsxr : σ x = r
    · by_cases hsxt : σ x = t
      · have : r = t := hsxr.symm.trans hsxt
        subst this
        simp [Equiv.swap_apply_def, hsxr]
      · simp [Equiv.swap_apply_def, hsxr, hsxt]
    · by_cases hsxt : σ x = t
      · simp [Equiv.swap_apply_def, hsxr, hsxt]
      · simp [Equiv.swap_apply_def, hsxr, hsxt]
  · intro σ _hσ
    ext x
    simp [Equiv.trans_apply]
    by_cases hsxt : σ x = t
    · by_cases hsxr : σ x = r
      · have : t = r := hsxt.symm.trans hsxr
        subst this
        simp [Equiv.swap_apply_def, hsxt]
      · simp [Equiv.swap_apply_def, hsxr, hsxt]
    · by_cases hsxr : σ x = r
      · simp [Equiv.swap_apply_def, hsxr, hsxt]
      · simp [Equiv.swap_apply_def, hsxr, hsxt]

def latestChoice {n : CandidateCount}
    (s : Finset (Fin n.succ)) (hs : s.Nonempty) (σ : Equiv.Perm (Fin n.succ)) : Fin n.succ :=
  Classical.choose (existsUnique_latestIn σ s hs).exists

theorem latestChoice_spec {n : CandidateCount}
    (s : Finset (Fin n.succ)) (hs : s.Nonempty) (σ : Equiv.Perm (Fin n.succ)) :
    latestIn σ s (latestChoice s hs σ) := by
  exact (Classical.choose_spec (existsUnique_latestIn σ s hs).exists)

theorem latestChoice_mem {n : CandidateCount}
    (s : Finset (Fin n.succ)) (hs : s.Nonempty) (σ : Equiv.Perm (Fin n.succ)) :
    latestChoice s hs σ ∈ s := by
  exact (latestChoice_spec s hs σ).1

theorem latestChoice_eq_iff {n : CandidateCount}
    (s : Finset (Fin n.succ)) (hs : s.Nonempty) (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) :
    latestChoice s hs σ = r ↔ latestIn σ s r := by
  constructor
  · intro h
    subst h
    exact latestChoice_spec s hs σ
  · intro hr
    exact latestIn_unique σ s (latestChoice_spec s hs σ) hr

theorem sum_card_filter_latestIn
    {n : CandidateCount} (s : Finset (Fin n.succ)) (hs : s.Nonempty) :
    ∑ r in s, (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card =
      Fintype.card (Equiv.Perm (Fin n.succ)) := by
  classical
  calc
    ∑ r in s, (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card
      = ∑ r in s, (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestChoice s hs σ = r).card := by
          apply Finset.sum_congr rfl
          intro r _hr
          congr
          ext σ
          simp [latestChoice_eq_iff]
    _ = (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestChoice s hs σ ∈ s).card := by
          exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ s (latestChoice s hs)
    _ = Fintype.card (Equiv.Perm (Fin n.succ)) := by
          simp [latestChoice_mem]

theorem card_filter_latestIn_eq_card_div
    {n : CandidateCount} (s : Finset (Fin n.succ)) (hs : s.Nonempty) (r : Fin n.succ) (hr : r ∈ s) :
    s.card * (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card =
      Fintype.card (Equiv.Perm (Fin n.succ)) := by
  have hconst :
      ∀ t ∈ s,
        (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s t).card =
          (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card := by
    intro t ht
    symm
    exact card_filter_latestIn_eq s hs hr ht
  calc
    s.card * (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s r).card
      = ∑ t in s, (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ s t).card := by
          exact (Finset.sum_const_nat hconst).symm
    _ = Fintype.card (Equiv.Perm (Fin n.succ)) := by
          exact sum_card_filter_latestIn s hs

/-! ### Part II: subset events and coefficients

This second block turns the latest-in symmetry into the exact probability of
the event `t ⊆ beforeSet σ r`, and then packages that coefficient for the PMF
bridge in `Paper.ClosedForm`.
-/

theorem latestIn_insert_iff {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) (t : Finset (Fin n.succ))
    (hr : r ∉ t) :
    latestIn σ (insert r t) r ↔ ∀ i ∈ t, σ.symm i < σ.symm r := by
  constructor
  · intro h i hi
    rcases h with ⟨_, hle⟩
    have hne : i ≠ r := by
      intro hir
      exact hr (hir ▸ hi)
    have hle' : σ.symm i ≤ σ.symm r := hle i (by simp [hi])
    exact lt_of_le_of_ne hle' (by
      intro heq
      apply hne
      exact σ.symm.injective heq)
  · intro h
    refine ⟨by simp, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact le_rfl
    · exact (h i hi').le

def latestInCount {n : CandidateCount} (r : Fin n.succ) (t : Finset (Fin n.succ)) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n.succ) => latestIn σ (insert r t) r).card

/-- Uniform mass assigned to the event that `r` is latest in `insert r t`. -/
def latestInMass {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) (t : Finset (Fin n.succ)) : ENNReal :=
  ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) : PMF (Equiv.Perm (Fin n.succ))) σ) *
    (latestInCount r t : ENNReal)

def beforeSet {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) : Finset (Fin n.succ) :=
  (Finset.univ.erase r).filter fun i => σ.symm i < σ.symm r

theorem latestInMass_eq_inv_card_insert
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) (t : Finset (Fin n.succ))
    (_hr : r ∉ t) :
    latestInMass σ r t = (((insert r t).card : ENNReal)⁻¹) := by
  classical
  have hs : (insert r t).Nonempty := by simp
  have hcount :
      (insert r t).card * latestInCount r t = Fintype.card (Equiv.Perm (Fin n.succ)) := by
    simpa [latestInCount] using card_filter_latestIn_eq_card_div (insert r t) hs r (by simp)
  have hcard_ne : ((insert r t).card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  have htot_ne : (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n.succ)) ≠ 0)
  have hcount_cast :
      ((insert r t).card : ENNReal) * (latestInCount r t : ENNReal) =
        (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal) := by
    exact_mod_cast hcount
  have hcount' : ((latestInCount r t : ℕ) : ENNReal) = ((insert r t).card : ENNReal)⁻¹ *
      (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal) := by
    calc
      ((latestInCount r t : ℕ) : ENNReal)
        = ((insert r t).card : ENNReal)⁻¹ * (((insert r t).card : ENNReal) * (latestInCount r t : ENNReal)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hcard_ne (by simp), one_mul]
      _ = ((insert r t).card : ENNReal)⁻¹ *
            (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal) := by
            rw [hcount_cast]
  calc
    latestInMass σ r t
      = (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)⁻¹ * (latestInCount r t : ENNReal) := by
          simp [latestInMass, latestInCount, PMF.uniformOfFintype_apply]
    _ = (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)⁻¹ *
          (((insert r t).card : ENNReal)⁻¹ *
            (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)) := by
          rw [hcount']
    _ = ((insert r t).card : ENNReal)⁻¹ := by
          calc
            (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)⁻¹ *
                (((insert r t).card : ENNReal)⁻¹ *
                  (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal))
              = ((insert r t).card : ENNReal)⁻¹ *
                  ((Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)⁻¹ *
                    (Fintype.card (Equiv.Perm (Fin n.succ)) : ENNReal)) := by
                      ac_rfl
            _ = ((insert r t).card : ENNReal)⁻¹ * 1 := by
                  rw [ENNReal.inv_mul_cancel htot_ne (by simp)]
            _ = ((insert r t).card : ENNReal)⁻¹ := by rw [mul_one]

theorem subset_beforeSet_iff_latestIn_insert
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) (t : Finset (Fin n.succ))
    (hr : r ∉ t) :
    t ⊆ beforeSet σ r ↔ latestIn σ (insert r t) r := by
  constructor
  · intro hsub
    rw [latestIn_insert_iff σ r t hr]
    intro i hi
    have hi' : i ∈ beforeSet σ r := hsub hi
    simp [beforeSet] at hi'
    exact hi'.2
  · intro h
    rw [latestIn_insert_iff σ r t hr] at h
    intro i hi
    have hir : i ≠ r := by
      intro hir
      exact hr (hir ▸ hi)
    simp [beforeSet, hir, hi, h i hi]

theorem latestInMass_eq_inv_card_succ
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) (t : Finset (Fin n.succ))
    (hr : r ∉ t) :
    latestInMass σ r t = ((t.card + 1 : ℕ) : ENNReal)⁻¹ := by
  rw [latestInMass_eq_inv_card_insert σ r t hr]
  rw [Finset.card_insert_of_not_mem hr]

theorem indexOf_map_canonicalOrder
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) :
    (((List.finRange n.succ).map σ).indexOf r) = (σ.symm r).1 := by
  have hlen : (σ.symm r).1 < (((List.finRange n.succ).map σ)).length := by
    simp
  calc
    (((List.finRange n.succ).map σ).indexOf r : ℕ)
      = (((List.finRange n.succ).map σ)[(σ.symm r).1]'hlen
          |> fun x => ((List.finRange n.succ).map σ).indexOf x) := by
            simp [List.getElem_map, hlen]
    _ = (σ.symm r).1 := by
      exact List.indexOf_getElem
        (l := ((List.finRange n.succ).map σ))
        (H := by simpa using (List.nodup_finRange n.succ).map σ.injective)
        (i := (σ.symm r).1)
        (h := hlen)

theorem take_ofFn_eq_ofFn_prefix
    {α : Type} {n : ℕ} (f : Fin n → α) (k : Fin n) :
    (List.ofFn f).take k = List.ofFn (fun j : Fin k => f ⟨j, Nat.lt_trans j.2 k.2⟩) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hk : (i : ℕ) < (k : ℕ) := by
      simpa [List.length_ofFn] using hi₂
    have hi_len : (i : ℕ) < (List.ofFn f).length := by
      simpa [List.length_ofFn] using Nat.lt_trans hk k.2
    calc
      (List.take (k : ℕ) (List.ofFn f))[i]
        = (List.ofFn f)[i] := by
            symm
            exact List.getElem_take (L := List.ofFn f) hi_len hk
      _ = f ⟨i, by simpa [List.length_ofFn] using hi_len⟩ := by
            simp [List.getElem_ofFn]
      _ = (List.ofFn fun j : Fin k => f ⟨j, Nat.lt_trans j.2 k.2⟩)[i] := by
            simp [List.getElem_ofFn, hk]

def beforeEmbedding {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) : Fin (σ.symm r) ↪ Fin n.succ where
  toFun j := σ ⟨j, Nat.lt_trans j.2 (σ.symm r).2⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    simpa using congrArg Fin.val (σ.injective hab)

theorem beforeSet_eq_map_beforeEmbedding
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) :
    beforeSet σ r = Finset.univ.map (beforeEmbedding σ r) := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_filter.mp hi with ⟨_hi_univ, hi_lt⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨(σ.symm i).1, hi_lt⟩, ?_, ?_⟩
    · simp
    · simp [beforeEmbedding]
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hji⟩
    have hsymm : σ.symm i = ⟨(j : ℕ), Nat.lt_trans j.2 (σ.symm r).2⟩ := by
      apply σ.injective
      simpa [beforeEmbedding] using hji.symm
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_erase.mpr ?_
      constructor
      · intro hir
        have hlt : σ.symm i < σ.symm r := by
          rw [hsymm]
          exact j.2
        have : σ.symm r < σ.symm r := by
          have : False := by
            simp [hir] at hlt
          exact False.elim this
        exact lt_irrefl _ this
      · simp
    · rw [hsymm]
      exact j.2

theorem prefix_prod_eq_beforeSet_prod
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ)
    (g : Fin n.succ → ENNReal) :
    (((List.ofFn σ).take (σ.symm r)).map g).prod = ∏ i in beforeSet σ r, g i := by
  rw [take_ofFn_eq_ofFn_prefix σ (σ.symm r), List.map_ofFn, List.prod_ofFn]
  rw [beforeSet_eq_map_beforeEmbedding σ r]
  rw [Finset.prod_map]
  rfl

/-! ### Part III: coefficients specialized to the paper probabilities -/

@[simp]
theorem ofReal_one_sub_paperProb_eq_exactCoin_false {n : CandidateCount}
    (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (i : Fin n.succ) :
    ENNReal.ofReal (1 - paperProb q ε₁ ε₂ i) = exactCoinPMF (gap q i * ε₁) ε₂ false := by
  rw [exactCoinPMF_apply_false, paperProb]
  have hnonneg :
      0 ≤ Real.exp (- ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) := by
    positivity
  simpa using (ENNReal.ofReal_sub (1 : ℝ) hnonneg)

theorem paperProb_nonneg {n : CandidateCount}
    (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (i : Fin n.succ) :
    0 ≤ paperProb q ε₁ ε₂ i := by
  unfold paperProb
  positivity

theorem paperProb_le_one {n : CandidateCount}
    (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (i : Fin n.succ) :
    paperProb q ε₁ ε₂ i ≤ 1 := by
  unfold paperProb
  have hnonneg : 0 ≤ ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by positivity
  have hle : Real.exp (- ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ Real.exp 0 := by
    exact Real.exp_le_exp.mpr (by linarith)
  simpa using hle

theorem beforeSet_subset_erase {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) :
    beforeSet σ r ⊆ Finset.univ.erase r := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem powerset_beforeSet_eq_filter
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ) :
    (beforeSet σ r).powerset =
      ((Finset.univ.erase r).powerset).filter (fun t => t ⊆ beforeSet σ r) := by
  ext t
  constructor
  · intro ht
    simp [Finset.mem_powerset] at ht ⊢
    exact ⟨Set.Subset.trans ht (beforeSet_subset_erase σ r), ht⟩
  · intro ht
    simp [Finset.mem_powerset] at ht ⊢
    exact ht.2

theorem sum_powerset_beforeSet_eq_sum_filter
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (r : Fin n.succ)
    (F : Finset (Fin n.succ) → ℝ) :
    ∑ t in (beforeSet σ r).powerset, F t =
      ∑ t in (Finset.univ.erase r).powerset, if t ⊆ beforeSet σ r then F t else 0 := by
  rw [powerset_beforeSet_eq_filter σ r, Finset.sum_filter]

theorem real_subset_beforeSet_coeff
    {n : CandidateCount} (r : Fin n.succ) (t : Finset (Fin n.succ))
    (hr : r ∉ t) :
    ∑ σ : Equiv.Perm (Fin n.succ),
      (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
      (if t ⊆ beforeSet σ r then 1 else 0)
      = ((t.card + 1 : ℕ) : ℝ)⁻¹ := by
  let u : ℝ := (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) (Equiv.refl (Fin n.succ))).toReal
  have hu : ∀ σ : Equiv.Perm (Fin n.succ),
      (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal = u := by
    intro σ
    simp [u, PMF.uniformOfFintype_apply]
  calc
    ∑ σ : Equiv.Perm (Fin n.succ),
        (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
          (if t ⊆ beforeSet σ r then 1 else 0)
      = u * ∑ σ : Equiv.Perm (Fin n.succ), (if t ⊆ beforeSet σ r then 1 else 0) := by
          -- Under the uniform distribution on permutations, every permutation
          -- has the same mass `u`, so only the event count matters.
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _hσ
          rw [hu σ]
    _ = u * latestInCount r t := by
          -- The event "`t` appears before `r`" is the same as "`r` is latest in `insert r t`".
          simp [latestInCount, subset_beforeSet_iff_latestIn_insert, hr]
    _ = ((t.card + 1 : ℕ) : ℝ)⁻¹ := by
          -- `latestInMass_eq_inv_card_succ` is exactly the equal-share counting
          -- statement: among the `t.card + 1` elements of `insert r t`, each is
          -- equally likely to be the latest one.
          have hmass :=
            congrArg ENNReal.toReal
              (latestInMass_eq_inv_card_succ (σ := Equiv.refl (Fin n.succ)) r t hr)
          have htoRealInv : ((((t.card + 1 : ℕ) : ENNReal)⁻¹).toReal) = ((t.card + 1 : ℕ) : ℝ)⁻¹ := by
            simpa using ENNReal.toReal_inv ((t.card + 1 : ℕ) : ENNReal)
          rw [htoRealInv] at hmass
          simpa [u, latestInMass, PMF.uniformOfFintype_apply] using hmass

theorem prod_neg_paperProb
    {n : CandidateCount} (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (t : Finset (Fin n.succ)) :
    ∏ i in t, (-paperProb q ε₁ ε₂ i) =
      ((-1 : ℝ) ^ t.card) * ∏ i in t, paperProb q ε₁ ε₂ i := by
  calc
    ∏ i in t, (-paperProb q ε₁ ε₂ i)
      = ∏ i in t, ((-1 : ℝ) * paperProb q ε₁ ε₂ i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          ring
    _ = (∏ _i in t, (-1 : ℝ)) * ∏ i in t, paperProb q ε₁ ε₂ i := by
          rw [Finset.prod_mul_distrib]
    _ = ((-1 : ℝ) ^ t.card) * ∏ i in t, paperProb q ε₁ ε₂ i := by
          rw [Finset.prod_const]

theorem paperAlt_eq_sum_neg_prod
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    paperAlt q r ε₁ ε₂ =
      ∑ t in (Finset.univ.erase r).powerset,
        (((t.card + 1 : ℕ) : ℝ)⁻¹) * ∏ i in t, (-paperProb q ε₁ ε₂ i) := by
  unfold paperAlt
  apply Finset.sum_congr rfl
  intro t _ht
  rw [prod_neg_paperProb q ε₁ ε₂ t]
  have hne : ((t.card : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hne]

theorem paperProb_bumpScore_other_of_gap_zero
    {n : CandidateCount} (q : Scores n) (r i : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hir : i ≠ r) (hgap : gap q r = 0) :
    paperProb (bumpScore q r 1) ε₁ ε₂ i =
      Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) * paperProb q ε₁ ε₂ i := by
  unfold paperProb
  rw [gap_bumpScore_other_of_gap_zero q r i 1 hir hgap]
  rw [Nat.add_mul, one_mul]
  have hdiv :
      ((((gap q i * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) =
        ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) +
          ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by
    have hden : (((ε₂ : NNReal) : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
  have hdiv' :
      - ((((gap q i * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) =
        - ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) +
          - ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by
            linarith
  change
    Real.exp (- ((((gap q i * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) =
      Real.exp (- ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) *
        Real.exp (- ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ))
  rw [hdiv', Real.exp_add]

theorem paperAlt_bumpScore_self_one_of_gap_zero
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hgap : gap q r = 0) :
    paperAlt (bumpScore q r 1) r ε₁ ε₂ =
      paperAltScaled q r ε₁ ε₂ (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) := by
  unfold paperAlt paperAltScaled
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ⊆ Finset.univ.erase r := by
    simpa using (Finset.mem_powerset.mp ht)
  have hrnot : r ∉ t := by
    exact fun hrmem => (Finset.mem_erase.mp (ht' hrmem)).1 rfl
  calc
    (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ∏ i in t, paperProb (bumpScore q r 1) ε₁ ε₂ i
      = (((-1 : ℝ) ^ t.card) / (t.card + 1)) *
          ∏ i in t, (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) * paperProb q ε₁ ε₂ i) := by
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            apply paperProb_bumpScore_other_of_gap_zero
            intro hir
            exact hrnot (hir ▸ hi)
            exact hgap
    _ = (((-1 : ℝ) ^ t.card) / (t.card + 1)) *
          ((∏ _i in t, Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) *
            ∏ i in t, paperProb q ε₁ ε₂ i) := by
              rw [Finset.prod_mul_distrib]
    _ = (((-1 : ℝ) ^ t.card) / (t.card + 1)) *
          (((Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) ^ t.card) *
            ∏ i in t, paperProb q ε₁ ε₂ i) := by
              rw [Finset.prod_const]
    _ = (((-1 : ℝ) ^ t.card) / (t.card + 1)) *
          (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) ^ t.card) *
            ∏ i in t, paperProb q ε₁ ε₂ i := by
              ring

theorem paperProb_lowerScore_other_of_unique_max_one
    {n : CandidateCount} (q : Scores n) (s i : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (his : i ≠ s) (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    paperProb q ε₁ ε₂ i =
      Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) *
        paperProb (lowerScore q s 1) ε₁ ε₂ i := by
  have hmaxq : maxScore q = q s := maxScore_eq_of_unique_max q s huniq
  have hgap_pos : 0 < gap q i := by
    rw [gap_eq_maxScore_sub, hmaxq]
    exact Nat.sub_pos_of_lt (huniq i his)
  have hgap_one : 1 ≤ gap q i := Nat.succ_le_of_lt hgap_pos
  unfold paperProb
  rw [gap_lowerScore_other_of_unique_max_one q s i his huniq]
  have hmul :
      (gap q i * ε₁ : ℕ) = (gap q i - 1) * ε₁ + ε₁ := by
    calc
      gap q i * ε₁ = ((gap q i - 1) + 1) * ε₁ := by
        rw [Nat.sub_add_cancel hgap_one]
      _ = (gap q i - 1) * ε₁ + ε₁ := by ring
  rw [hmul]
  have hdiv :
      (((((gap q i - 1) * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) =
        (((((gap q i - 1) * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) +
          ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by
    have hden : (((ε₂ : NNReal) : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
  have hdiv' :
      - (((((gap q i - 1) * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) =
        - ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) +
          - (((((gap q i - 1) * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by
    linarith
  change
    Real.exp (- (((((gap q i - 1) * ε₁ + ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) =
      Real.exp (- ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) *
        Real.exp (- (((((gap q i - 1) * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ))
  rw [hdiv', Real.exp_add]

theorem paperAlt_eq_paperAltGapZeroScaled_lowerScore_unique_max_one
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    paperAlt q r ε₁ ε₂ =
      paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂
        (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) := by
  have hs : gap q s = 0 := by
    rw [gap_eq_maxScore_sub, maxScore_eq_of_unique_max q s huniq]
    simp
  rw [paperAlt_eq_sum_erase_gap_zero q r s ε₁ ε₂ hrs.symm hs]
  unfold paperAltGapZeroScaled
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
        ∏ i in t, paperProb q ε₁ ε₂ i
      = (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          ∏ i in t,
            (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) *
              paperProb (lowerScore q s 1) ε₁ ε₂ i) := by
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            apply paperProb_lowerScore_other_of_unique_max_one
            intro his
            have : s ∈ ((Finset.univ.erase r).erase s) := (Finset.mem_powerset.mp ht) (his ▸ hi)
            simp at this
            exact huniq
    _ = (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          ((∏ _i in t, Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) *
            ∏ i in t, paperProb (lowerScore q s 1) ε₁ ε₂ i) := by
              rw [Finset.prod_mul_distrib]
    _ = (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          ((Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) ^ t.card) *
            ∏ i in t, paperProb (lowerScore q s 1) ε₁ ε₂ i) := by
              rw [Finset.prod_const]
    _ = (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) ^ t.card) *
            ∏ i in t, paperProb (lowerScore q s 1) ε₁ ε₂ i := by
              ring


end PermuteAndFlip
end SLang
