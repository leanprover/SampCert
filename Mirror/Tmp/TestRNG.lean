import Init.System.IO
import Mirror.H1

def test1 (f: Nat → Nat) (n : Nat) : StateM (Nat → Option Nat) Nat := do
  let state : Nat → Option Nat ← get
  match state n with
  | some v => return v
  | none => {
    let r := f n
    let f : Nat → Option Nat := λ m : Nat => if n = m then some r else state m;
    set f
    return r
  }

def test2 : StateT ByteArray IO UInt8 := do
  let state ← get
  let r : ByteArray ← IO.getRandomBytes 1
  set (state ++ r)
  return r[0]!

def test3 : ExceptT String (StateT ByteArray IO) UInt8 := do
  let state ← get
  let r : ByteArray ← IO.getRandomBytes 1
  if r.size != 1
    then throw "Something went wrong"
    else {
      set (state ++ r)
      return r[0]!
    }

def test4 : ExceptT String (StateT ByteArray IO) UInt8 := do
  let state ← get
  let r : ByteArray ← IO.getRandomBytes 1
  match r[0]? with
  | some v => {
    set (state ++ r)
    return v
  }
  | none => throw "Something went wrong"

-- set_option pp.implicit true

set_option pp.all true

def f : ExceptT String (StateT Nat Option) Bool := sorry
def g : StateT Nat Option Bool := sorry

theorem ex1 : f = g := sorry
theorem ex2 : f = ↑g := sorry
