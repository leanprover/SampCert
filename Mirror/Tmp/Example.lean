import Mirror.Export
import Mirror.Align
import Mirror.Print

-- Map a Lean concept to Dafny
attribute [align_dafny "nat"] Nat

-- Translate to Dafny

def k := 2
def f (x: Nat) : Nat := x

-- Exporter currently ignores custom name
@[export_dafny "simple1D"]
theorem simple1 : f 2 = k := by
  rfl

-- Get result
#print_dafny_exports
