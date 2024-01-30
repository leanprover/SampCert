import Mirror.Export
import Mirror.Align
import Mirror.Print

import Mathlib.Init.ZeroOne
import Mathlib.Data.Nat.Basic

import Mathlib.MeasureTheory.MeasurableSpace.Defs

import Lean.Meta

attribute [align_dafny "nat"] Nat
attribute [align_dafny "MeasurableSpace"] MeasurableSpace

--set_option trace.Elab.definition true
--set_option pp.explicit true
--set_option pp.universes true
--set_option pp.notation false

theorem test: 0 = 1 := by sorry

#check test

attribute [export_dafny "Foo"] test

#check Nat.zero_ne_one

attribute [export_dafny "Bar"] Nat.zero_ne_one

theorem test2: forall x: Nat, x == x := by sorry

--attribute [export_dafny "Quux"] test2

#print_dafny_exports

#check Nat
#check Nat.add

inductive foo
class bar

-- #print Monoid
#check Nat.commSemiring

def x : Nat := 42
#check Lean.Meta.isInstance

-- attribute [export_dafny "Zetch"] Nat.commSemiring
-- attribute [export_dafny "Zetch"] Group
-- attribute [export_dafny "AAAA"] foo
-- attribute [export_dafny "AAAA"] bar
