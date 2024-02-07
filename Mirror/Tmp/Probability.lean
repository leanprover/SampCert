import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Measure ENNReal

def BitStream : Type := Nat → Bool

def Events: Set BitStream → Prop := sorry

theorem A1: Events ∅ := sorry
theorem A2: ∀ (s : Set BitStream), Events s → Events sᶜ := sorry
theorem A3: ∀ (f : ℕ → Set BitStream), (∀ (i : ℕ), Events (f i)) → Events (⋃ i, f i) := sorry

instance Cl1 : MeasurableSpace BitStream :=
  by
    apply MeasurableSpace.mk Events
    apply A1
    apply A2
    apply A3

def Mu: Set BitStream → ℝ≥0∞ := sorry

theorem B1: Mu ∅ = 0 := sorry
theorem B2: ∀ {s₁ s₂ : Set BitStream}, s₁ ⊆ s₂ → Mu s₁ ≤ Mu s₂ := sorry
theorem B3: ∀ (s : ℕ → Set BitStream), Mu (⋃ i, s i) ≤ ∑' (i : ℕ), Mu (s i) := sorry

instance Cl2 : OuterMeasure BitStream :=
  by
    apply OuterMeasure.mk Mu
    apply B1
    apply B2
    apply B3

theorem C1: ∀ ⦃f : ℕ → Set BitStream⦄,
  (∀ (i : ℕ), MeasurableSet (f i)) → Pairwise (Disjoint on f) → Cl2 (⋃ i, f i) = ∑' (i : ℕ), Cl2 (f i) := sorry
theorem C2: OuterMeasure.trim Cl2 = Cl2 := sorry

instance Cl3 : Measure BitStream :=
  by
    apply Measure.mk Cl2
    apply C1
    apply C2

instance Cl4 : MeasureSpace BitStream :=
  by
    apply MeasureSpace.mk Cl3


-- Constructing measures

#check Measure.ofMeasurable
#check OuterMeasure.toMeasure

#check OuterMeasure.caratheodory


def Head (s : BitStream) : Bool :=
  s 0

def Tail (s : BitStream) : BitStream :=
  λ n : Nat => s (n + 1)

theorem test1: Cl3 { s : BitStream | Head s = True } = 1 / 2 := sorry
theorem test2: Mu { s : BitStream | Head s = True } = 1 / 2 := sorry

def Hurd (T : Type) : Type := BitStream → T × BitStream

instance H : Monad Hurd where
  pure := λ { T : Type } => λ x : T => λ s : BitStream => (x,s)
  bind := λ { T U : Type } => λ f : Hurd T => λ g : T → Hurd U => λ s : BitStream => let (v,s') := f s ; (g v) s'

def Coin : Hurd Bool := λ s : BitStream => (s 0, λ n : Nat => s (n + 1))

def FourSided : Hurd Nat := do
  let c1 ← Coin
  let c2 ← Coin
  let tov := λ b : Bool => if b then 1 else 0;
  return (tov c1) + 2 * (tov c2)

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

noncomputable def PushHurd {T : Type} [MeasurableSpace T] (h: Hurd T) : Measure T := map (λ s : BitStream => fst (h s)) Cl4.volume

theorem Eq1 {T : Type} [MeasurableSpace T] :
  forall x : T, PushHurd (H.pure x) = dirac x := sorry

theorem Eq2 {T U : Type} [MeasurableSpace T] [MeasurableSpace U] :
  forall f : Hurd T, forall g : T → Hurd U,
  PushHurd (H.bind f g) = MeasureTheory.Measure.bind (PushHurd f) (λ t : T => PushHurd (g t)) := sorry

def Giry (T : Type) [MeasurableSpace T] : Type := Measure T

instance [MeasurableSpace T] H2 : Monad ((λ T : Type => @Giry T H) T) where
  pure := dirac
  bind := MeasureTheory.Measure.bind
