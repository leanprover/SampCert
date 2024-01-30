import Mirror.H2
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Measure ENNReal

#check dirac
#check MeasureTheory.Measure.bind

section Tr

variable {T U : Type}
variable [MeasurableSpace T] [MeasurableSpace U]

@[simp]
noncomputable def Push (h: Hurd T) : Measure T := map (λ s : BitStream => (h s).1) Prob.volume

@[simp]
noncomputable def DCoin : Measure Bool := Push Coin

@[simp]
noncomputable def DPure (x : T) : Measure T := Push (H.pure x)

#check map_apply
#check dirac

theorem Corr1 (x : T) (S : Set T) : DPure x S = dirac x S := sorry

noncomputable def DBind (f: Hurd T) (g : T → Hurd U) : Measure U := Push (H.bind f g)

end Tr
