import SampCert.DifferentialPrivacy.PermuteAndFlip.Privacy

noncomputable section

open scoped Classical

namespace SLang
namespace PermuteAndFlip

abbrev ScoreMechanism (n : CandidateCount) (U : Type) := Scores n → SLang U

/-- Adaptive composition, written directly in pointwise form. -/
def scoreComposeAdaptive {n : CandidateCount}
    (m₁ : ScoreMechanism n U) (m₂ : U → ScoreMechanism n V) :
    ScoreMechanism n (U × V) :=
  fun q uv => m₁ q uv.1 * m₂ uv.1 q uv.2

/-- Postprocessing, written as the fiberwise pushforward of a distribution. -/
def scorePostprocess {n : CandidateCount}
    (m : ScoreMechanism n U) (f : U → V) :
    ScoreMechanism n V :=
  fun q v => ∑' u : U, if f u = v then m q u else 0

/-- Pointwise privacy under the range metric, with budget `steps`. -/
def RangePrivate {n : CandidateCount} (α : ENNReal) (steps : ℕ)
    (m : ScoreMechanism n U) : Prop :=
  ∀ q q' u,
    α ^ (steps * rangeDistance q q') * m q u ≤ m q' u

namespace RangePrivate

@[simp] theorem const {n : CandidateCount} (α : ENNReal) (u : U) :
    RangePrivate α 0 (fun _ : Scores n => SLang.probPure u) := by
  intro q q' x
  simp [RangePrivate, SLang.probPure]

theorem const_of_le_one {n : CandidateCount} {α : ENNReal} {steps : ℕ}
    (hα : α ≤ 1) (u : U) :
    RangePrivate α steps (fun _ : Scores n => SLang.probPure u) := by
  intro q q' x
  by_cases hx : x = u
  · subst hx
    have hpow : α ^ (steps * rangeDistance q q') ≤ 1 := by
      exact pow_le_one' hα _
    simpa [SLang.probPure] using hpow
  · simp [SLang.probPure, hx]

@[simp] theorem composeAdaptive {n : CandidateCount}
    {α : ENNReal} {s₁ s₂ : ℕ}
    {m₁ : ScoreMechanism n U} {m₂ : U → ScoreMechanism n V}
    (h₁ : RangePrivate α s₁ m₁)
    (h₂ : ∀ u, RangePrivate α s₂ (m₂ u)) :
    RangePrivate α (s₁ + s₂) (scoreComposeAdaptive m₁ m₂) := by
  intro q q' uv
  rcases uv with ⟨u, v⟩
  let d := rangeDistance q q'
  have hm₁ := h₁ q q' u
  have hm₂ := h₂ u q q' v
  calc
    α ^ ((s₁ + s₂) * d) * scoreComposeAdaptive m₁ m₂ q (u, v)
        = (α ^ (s₁ * d) * m₁ q u) * (α ^ (s₂ * d) * m₂ u q v) := by
            simp [scoreComposeAdaptive, d, Nat.add_mul, pow_add,
              mul_assoc, mul_left_comm, mul_comm]
    _ ≤ m₁ q' u * m₂ u q' v := by
      exact mul_le_mul' hm₁ hm₂
    _ = scoreComposeAdaptive m₁ m₂ q' (u, v) := by
      simp [scoreComposeAdaptive]

@[simp] theorem postprocess {n : CandidateCount}
    {α : ENNReal} {steps : ℕ}
    {m : ScoreMechanism n U} (h : RangePrivate α steps m)
    (f : U → V) :
    RangePrivate α steps (scorePostprocess m f) := by
  intro q q' v
  let γ := α ^ (steps * rangeDistance q q')
  calc
    γ * scorePostprocess m f q v
        = γ * ∑' u : U, if f u = v then m q u else 0 := by
            simp [scorePostprocess]
    _ = ∑' u : U, γ * (if f u = v then m q u else 0) := by
          symm
          exact ENNReal.tsum_mul_left
    _ = ∑' u : U, if f u = v then m q u * γ else 0 := by
          refine tsum_congr ?_
          intro u
          by_cases hu : f u = v
          · simp [hu, mul_comm]
          · simp [hu]
    _ ≤ ∑' u : U, if f u = v then m q' u else 0 := by
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : f u = v
      · simpa [hu, γ, mul_assoc, mul_left_comm, mul_comm] using h q q' u
      · simp [hu]
    _ = scorePostprocess m f q' v := by
      simp [scorePostprocess]

end RangePrivate

/-- `privacyBase` is always at most `1`, so larger exponents only make the factor smaller. -/
lemma privacyBase_le_one (ε₁ : ℕ) (ε₂ : ℕ+) : privacyBase ε₁ ε₂ ≤ 1 := by
  dsimp [privacyBase]
  refine ENNReal.ofReal_le_one.mpr ?_
  have hnonpos : -((((ε₁ : ℕ) : NNReal) / ε₂ : ℝ)) ≤ 0 := by
    have hnonneg : 0 ≤ ((((ε₁ : ℕ) : NNReal) / ε₂ : ℝ)) := by positivity
    linarith
  exact Real.exp_le_one_iff.mpr hnonpos

lemma privacyBase_pow_antitone {ε₁ : ℕ} {ε₂ : ℕ+} {a b : ℕ}
    (h : a ≤ b) :
    privacyBase ε₁ ε₂ ^ b ≤ privacyBase ε₁ ε₂ ^ a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  calc
    privacyBase ε₁ ε₂ ^ (a + c)
        = privacyBase ε₁ ε₂ ^ a * privacyBase ε₁ ε₂ ^ c := by
            rw [pow_add]
    _ ≤ privacyBase ε₁ ε₂ ^ a * 1 := by
      exact mul_le_mul_left' (pow_le_one' (privacyBase_le_one ε₁ ε₂) c) _
    _ = privacyBase ε₁ ε₂ ^ a := by simp

/-- Restrict a score vector to the candidates listed in `l`. -/
def restrictScores {n : CandidateCount} (q : Scores n)
    (l : List (Fin n.succ)) (hl : l ≠ []) : Scores (l.length - 1) :=
  fun i =>
    let hi : i.val < l.length := by
      have hpos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
      have hi0 : i.val < (l.length - 1).succ := i.is_lt
      omega
    q (l.get ⟨i.val, hi⟩)

/-- Lift an index in the restricted list back to the original candidate space. -/
def liftFromList {n : CandidateCount}
    (l : List (Fin n.succ)) (hl : l ≠ []) :
    Fin (l.length - 1).succ → Fin n.succ :=
  fun i =>
    let hi : i.val < l.length := by
      have hpos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
      have hi0 : i.val < (l.length - 1).succ := i.is_lt
      omega
    l.get ⟨i.val, hi⟩

@[simp] lemma restrictScores_eq_comp_lift {n : CandidateCount}
    (q : Scores n) (l : List (Fin n.succ)) (hl : l ≠ []) :
    restrictScores q l hl = fun i => q (liftFromList l hl i) := by
  rfl

/-- Removing coordinates cannot increase the range metric. -/
lemma rangeDistance_restrict_le {n : CandidateCount}
    (q q' : Scores n) (l : List (Fin n.succ)) (hl : l ≠ []) :
    rangeDistance (restrictScores q l hl) (restrictScores q' l hl)
      ≤ rangeDistance q q' := by
  let qr : Scores (l.length - 1) := restrictScores q l hl
  let qr' : Scores (l.length - 1) := restrictScores q' l hl
  have hmin : RangePrivacy.diffMin q q' ≤ RangePrivacy.diffMin qr qr' := by
    have hmem : RangePrivacy.diffMin qr qr' ∈ RangePrivacy.diffSet qr qr' :=
      Finset.min'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
    rw [← hi]
    simpa [qr, qr', restrictScores_eq_comp_lift] using
      (RangePrivacy.scoreDiff_mem_interval q q' (liftFromList l hl i)).1
  have hmax : RangePrivacy.diffMax qr qr' ≤ RangePrivacy.diffMax q q' := by
    have hmem : RangePrivacy.diffMax qr qr' ∈ RangePrivacy.diffSet qr qr' :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
    rw [← hi]
    simpa [qr, qr', restrictScores_eq_comp_lift] using
      (RangePrivacy.scoreDiff_mem_interval q q' (liftFromList l hl i)).2
  have hle :
      RangePrivacy.diffMax qr qr' - RangePrivacy.diffMin qr qr'
        ≤ RangePrivacy.diffMax q q' - RangePrivacy.diffMin q q' := by
    linarith
  dsimp [rangeDistance]
  exact Int.toNat_le_toNat hle

/-- Permute-and-flip on a fixed remaining candidate list, followed by the deterministic
map back to original candidate labels. -/
def subsetPermuteAndFlipSLang {n : CandidateCount}
    (l : List (Fin n.succ)) (hl : l ≠ [])
    (ε₁ : ℕ) (ε₂ : ℕ+) :
    ScoreMechanism n (Fin n.succ) :=
  scorePostprocess
    (fun q => permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂)
    (liftFromList l hl)

lemma subsetPermuteAndFlip_range_private {n : CandidateCount}
    (l : List (Fin n.succ)) (hl : l ≠ [])
    (ε₁ : ℕ) (ε₂ : ℕ+) :
    RangePrivate (privacyBase ε₁ ε₂) 1 (subsetPermuteAndFlipSLang l hl ε₁ ε₂) := by
  let α := privacyBase ε₁ ε₂
  have hcore : RangePrivate α 1
      (fun q => permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂) := by
    intro q q' r
    let d := rangeDistance q q'
    let dr := rangeDistance (restrictScores q l hl) (restrictScores q' l hl)
    have hpf : α ^ dr *
          permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂ r
            ≤
          permuteAndFlipSLang (l.length - 1) (restrictScores q' l hl) ε₁ ε₂ r := by
      simpa [α, dr] using
        permuteAndFlipSLang_range_privacy
          (q := restrictScores q l hl)
          (q' := restrictScores q' l hl)
          (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
    have hdr : dr ≤ d := rangeDistance_restrict_le q q' l hl
    have hpow : α ^ d ≤ α ^ dr := privacyBase_pow_antitone (ε₁ := ε₁) (ε₂ := ε₂) hdr
    have hmul : α ^ d *
          permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂ r
            ≤
          α ^ dr * permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂ r := by
      exact mul_le_mul_right' hpow _
    have hfinal : α ^ (1 * rangeDistance q q') *
          permuteAndFlipSLang (l.length - 1) (restrictScores q l hl) ε₁ ε₂ r
            ≤
          permuteAndFlipSLang (l.length - 1) (restrictScores q' l hl) ε₁ ε₂ r := by
      simpa [d] using le_trans hmul hpf
    exact hfinal
  simpa [subsetPermuteAndFlipSLang] using RangePrivate.postprocess hcore (liftFromList l hl)

/-- Peeling permute-and-flip over a list of remaining candidates. -/
def peelPermuteAndFlipSLangAux {n : CandidateCount}
    (l : List (Fin n.succ)) (k : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ScoreMechanism n (List (Fin n.succ)) :=
  match k with
  | 0 => fun _ => SLang.probPure []
  | k + 1 =>
      match l with
      | [] => fun _ => SLang.probPure []
      | a :: as =>
          scorePostprocess
            (scoreComposeAdaptive
              (subsetPermuteAndFlipSLang (a :: as) (by simp) ε₁ ε₂)
              (fun r => peelPermuteAndFlipSLangAux ((a :: as).erase r) k ε₁ ε₂))
            (fun z => z.1 :: z.2)

/-- Top-level peeling mechanism: start from the canonical candidate order. -/
def peelPermuteAndFlipSLang (n : CandidateCount)
    (k : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ScoreMechanism n (List (Fin n.succ)) :=
  peelPermuteAndFlipSLangAux (canonicalOrder n) k ε₁ ε₂

theorem peelPermuteAndFlipSLangAux_range_private {n : CandidateCount} :
    ∀ (l : List (Fin n.succ)), l.Nodup → ∀ (k : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+),
      RangePrivate (privacyBase ε₁ ε₂) k
        (peelPermuteAndFlipSLangAux l k ε₁ ε₂) := by
  intro l hl k
  induction k generalizing l with
  | zero =>
    intro ε₁ ε₂
    intro q q' ys
    by_cases hys : ys = [] <;>
      simp [RangePrivate, peelPermuteAndFlipSLangAux, SLang.probPure, hys]
  | succ k ih =>
      intro ε₁ ε₂
      cases l with
      | nil =>
          simpa [peelPermuteAndFlipSLangAux] using
            (RangePrivate.const_of_le_one
              (α := privacyBase ε₁ ε₂)
              (steps := k + 1)
              (privacyBase_le_one ε₁ ε₂)
              ([] : List (Fin n.succ)))
      | cons a as =>
          have hhead : RangePrivate (privacyBase ε₁ ε₂) 1
              (subsetPermuteAndFlipSLang (a :: as) (by simp) ε₁ ε₂) :=
            subsetPermuteAndFlip_range_private (a :: as) (by simp) ε₁ ε₂
          have htail : ∀ r,
              RangePrivate (privacyBase ε₁ ε₂) k
                (peelPermuteAndFlipSLangAux ((a :: as).erase r) k ε₁ ε₂) := by
            intro r
            exact ih ((a :: as).erase r) (hl.erase r) ε₁ ε₂
          simpa [peelPermuteAndFlipSLangAux, Nat.add_comm] using
            RangePrivate.postprocess
              (RangePrivate.composeAdaptive hhead htail)
              (fun z : Fin n.succ × List (Fin n.succ) => z.1 :: z.2)

/-- Privacy theorem for peeling permute-and-flip. The budget grows linearly in `k`,
matching the OpenDP implementation's composition accounting. -/
theorem peelPermuteAndFlipSLang_range_privacy {n : CandidateCount}
    (q q' : Scores n) (ys : List (Fin n.succ))
    (k : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    (privacyBase ε₁ ε₂) ^ (k * rangeDistance q q') *
      peelPermuteAndFlipSLang n k ε₁ ε₂ q ys
      ≤
      peelPermuteAndFlipSLang n k ε₁ ε₂ q' ys := by
  simpa [peelPermuteAndFlipSLang] using
    peelPermuteAndFlipSLangAux_range_private
      (l := canonicalOrder n)
      (by simpa [canonicalOrder] using List.nodup_finRange n.succ)
      (k := k) (ε₁ := ε₁) (ε₂ := ε₂)
      q q' ys

end PermuteAndFlip
end SLang
