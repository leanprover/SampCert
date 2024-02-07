import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecificLimits.Basic
import KolmogorovExtension4.CaratheodoryExtension

open Classical
open Set Classical ENNReal Function
open MeasureTheory MeasurableSpace Measure

def BitStream : Type := Nat → Bool

@[simp] def shd (s : BitStream) : Bool := s 0
@[simp] def stl (s : BitStream) : BitStream := λ n : Nat => s (n + 1)
@[simp] def scons (a : Bool) (s : BitStream) : BitStream := λ n : Nat => if n = 0 then a else s (n - 1)
def stake (n : Nat) (s : BitStream) : List Bool := if n = 0 then [] else shd s :: stake (n - 1) (stl s)
@[simp] def sdrop (n : Nat) (s : BitStream) : BitStream := if n = 0 then s else sdrop (n - 1) (stl s)
@[simp] def sdest (s : BitStream) : Bool × BitStream := (shd s, stl s)
@[simp] def mirror (s : BitStream) : BitStream := scons (! (shd s)) (stl s)

@[simp]
theorem Basic1 (h : Bool) (t : BitStream) : shd (scons h t) = h :=
  by
    simp

@[simp]
theorem Basic2 (h : Bool) (t : BitStream) : stl (scons h t) = t :=
  by
    unfold stl
    simp

@[simp]
theorem Basic3 (s : BitStream) : exists h : Bool, exists t : BitStream, s = scons h t :=
  by
    unfold scons
    exists shd s
    exists stl s
    funext
    rename_i x
    induction x <;> simp

@[simp]
theorem Basic4 (s : BitStream) : scons (shd s) (stl s) = s :=
  by
    unfold shd
    unfold stl
    unfold scons
    simp
    funext
    rename_i x
    induction x <;> simp

@[simp]
theorem Basic5 (h h' : Bool) (t t' : BitStream) : (scons h t = scons h' t') ↔ (h = h' ∧ t = t') :=
  by
    apply Iff.intro
    . intro H
      have Eq : (scons h t) 0 = (scons h' t') 0 := by
        rw [H]
      simp at Eq
      rw [← Eq] at H
      rw [← Eq]
      simp
      clear Eq h'
      by_contra Contra
      sorry
    . intro H
      cases H
      rename_i left right
      rw [left, right]

@[simp]
theorem Basic6 (s : BitStream) : mirror (mirror s) = s :=
  by
    simp
    eapply Basic4

@[simp]
theorem Basic7 (s : BitStream) : stl (mirror s) = stl s :=
  by
    simp

@[simp]
def prefix_set (l : List Bool) : Set BitStream := { s : BitStream | stake (List.length l) s = l }

def prefix_seq (l : List Bool) : BitStream :=
  match l with
  | [] => λ _ : Nat => False
  | hd :: tl => scons hd (prefix_seq tl)

def embed (l : List (List Bool)) : Set BitStream :=
  match l with
  | [] => ∅
  | hd :: tl => Set.union (prefix_set hd) (embed tl)

def BernoulliAlgebra : Set (Set BitStream) := { A : Set BitStream | exists l : List (List Bool), embed l = A}

theorem BernoulliAlgebraEmptyMem : ∅ ∈ BernoulliAlgebra := by
  have H : exists l : List (List Bool), embed l = ∅ := by
    exists []
  assumption

theorem BernoulliAlgebraInterMem : ∀ (s : Set BitStream), s ∈ BernoulliAlgebra → ∀ (t : Set BitStream), t ∈ BernoulliAlgebra → s ∩ t ∈ BernoulliAlgebra := by
  intro s Ins t Int
  unfold BernoulliAlgebra at *
  rw [mem_setOf] at *
  cases Ins
  rename_i ls Hs
  cases Int
  rename_i lt Ht
  rw [← Hs, ← Ht]
  sorry -- list of longest common prefix for every pair

theorem BernoulliDiffEqUnion :
  ∀ (s : Set BitStream), s ∈ BernoulliAlgebra →
  ∀ (t : Set BitStream), t ∈ BernoulliAlgebra →
  ∃ (I : Finset (Set BitStream)) (_h_ss : ↑I ⊆ BernoulliAlgebra) (_h_dis : PairwiseDisjoint (I : Set (Set BitStream)) id), t \ s = ⋃₀ ↑I := by
    intro s Ins t Int
    unfold BernoulliAlgebra at *
    rw [mem_setOf] at *
    cases Ins
    rename_i ls Hs
    cases Int
    rename_i lt Ht
    rw [← Hs, ← Ht]
    sorry -- [11] \ [1101] -> [1111] u [1100] u [1110] -- In BA, pairwise disjoint

instance BASR : MeasureTheory.SetSemiring BernoulliAlgebra where
  empty_mem := BernoulliAlgebraEmptyMem
  inter_mem := BernoulliAlgebraInterMem
  diff_eq_Union' := BernoulliDiffEqUnion

@[simp]
instance Eps : MeasurableSpace BitStream := generateFrom BernoulliAlgebra

theorem EpsIsBernoulliAlbegra : Eps = generateFrom BernoulliAlgebra :=
  by
    simp

noncomputable def μ₀ (l : List (List Bool)) : ℝ≥0∞ :=
  match l with
  | [] => 0
  | hd :: tl => 1 / 2 ^ ((List.length hd)) + μ₀ tl

noncomputable def μ₁ (A : Set BitStream) : ℝ≥0∞ := sInf { r : ℝ≥0∞ | exists l : List (List Bool), embed l = A ∧ μ₀ l = r }

theorem MeasEmpty : μ₁ ∅ = 0 := by
  unfold μ₁
  have H : 0 ∈ {r : ℝ≥0∞ | ∃ l, embed l = ∅ ∧ μ₀ l = r} := by
    rw [mem_setOf]
    exists []
  have H1 := sInf_le H
  have H2 : 0 ≤ sInf {r | ∃ l, embed l = ∅ ∧ μ₀ l = r} := by
    simp
  sorry

theorem MeasAdd :
  ∀ (I : Finset (Set BitStream)) (_h_ss : ↑I ⊆ BernoulliAlgebra)
  (_h_dis : PairwiseDisjoint (I : Set (Set BitStream)) id)
  (_h_mem : ⋃₀ ↑I ∈ BernoulliAlgebra),
    μ₁ (⋃₀ I) = Finset.sum I (fun u => μ₁ u) := sorry

noncomputable instance cont : AddContent BernoulliAlgebra where
  toFun := μ₁
  empty' := MeasEmpty
  add' := MeasAdd

theorem CountAdd : ∀ ⦃f : ℕ → Set BitStream⦄,
      (∀ (i : ℕ), f i ∈ BernoulliAlgebra) →
        ⋃ (i : ℕ), f i ∈ BernoulliAlgebra →
          (fun s => AddContent.toFun cont s) (⋃ (i : ℕ), f i) ≤ ∑' (i : ℕ), (fun s => AddContent.toFun cont s) (f i) := sorry

noncomputable instance μ : Measure BitStream := Measure.ofAddContent BASR EpsIsBernoulliAlbegra cont CountAdd

@[simp]
theorem TrimMeasure (s : Set BitStream) (_ : s ∈ BernoulliAlgebra) :  μ s = μ₁ s :=
  by
    apply Measure.ofAddContent_eq
    assumption

@[simp]
noncomputable instance Prob : MeasureSpace BitStream where
  volume := μ

@[simp]
instance : Membership (Set BitStream) (MeasureSpace BitStream) where
  mem := λ (A : Set BitStream) (F : MeasureSpace BitStream) => F.MeasurableSet' A

theorem Event1 (b: Bool) : { s : BitStream | shd s = b } ∈ BernoulliAlgebra :=
  by
    simp
    unfold BernoulliAlgebra
    simp
    exists [[b]]
    unfold embed
    unfold Set.union
    unfold embed
    simp
    unfold stake
    simp
    unfold stake
    simp

theorem Event1' (b: Bool) : { s : BitStream | shd s = b } ∈ Prob :=
  by
    simp
    apply measurableSet_generateFrom
    unfold BernoulliAlgebra
    simp
    exists [[b]]
    unfold embed
    unfold Set.union
    unfold embed
    simp
    unfold stake
    simp
    unfold stake
    simp

theorem Event2 (E : Set BitStream) : stl⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event3 (E : Set BitStream) : E ∈ Prob → stl '' E ∈ Prob := sorry

theorem Event4 (E : Set BitStream) (n : Nat) : (sdrop n) ⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event5 (E : Set BitStream) (n : Nat) : E ∈ Prob → (sdrop n) '' E ∈ Prob := sorry

theorem Event6 (b : Bool) : Measurable (scons b) := sorry

theorem Event7 (E : Set BitStream) (b : Bool) : (scons b) '' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Event8 (E : Set BitStream) : mirror ⁻¹' E ∈ Prob ↔ E ∈ Prob := sorry

theorem Prob1 (b : Bool) : Prob.volume { s : BitStream | shd s = b } = 1 / 2 :=
  by
    unfold volume
    simp
    rw [TrimMeasure]
    have H : μ₀ [[b]] = 1 / 2 :=
      by
      unfold μ₀
      unfold μ₀
      simp
    sorry
    apply Event1



def measure_preserving (f: BitStream → BitStream) : Prop :=
  Measurable f ∧ ∀ A : Set BitStream, A ∈ Prob → Prob.volume A = Prob.volume (f ⁻¹' A)

theorem Prob2 : measure_preserving stl := sorry

theorem Prob3 (n : Nat) : measure_preserving (sdrop n) := sorry

theorem Prob4 : measure_preserving mirror := sorry

theorem Prob5 (E : Set BitStream) : E ∈ Prob ∧ mirror '' E = E → Prob.volume (stl '' E) = Prob.volume E := sorry

theorem Final1 (n : Nat) : Prob.volume { s : BitStream | shd (sdrop n s) } = 1 /2 := sorry

theorem Final2 (m n : Nat) : Prob.volume { s : BitStream | shd (sdrop m s) = shd (sdrop n s)} = if m = n then 1 else 1 /2 := sorry
