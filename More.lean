def numBits (n : Nat) : Nat :=
  let left := n / 2
  if left = 0 then 1 else 1 + numBits left

--@[export super_sampler]
def foo (n : Nat) : IO Nat := do
  if n = 0 then
    panic s!"Cannot sample 0 bits"
  -- from least significant to most significant
  let numbits := numBits n
  --IO.println s!"Representation = {bits}"
  let want := numbits - 1
  --IO.println s!"Number of bits I want = {want}"
  let nbytes := want / 8 + 1
  --IO.println s!"Number of requested bytes = {nbytes}"
  let rbytes ← IO.getRandomBytes nbytes.toUSize
  --for b in rbytes do
  --   IO.println s!"{b.toNat.bits}"
  let head := (rbytes.get! 0).toNat
  --IO.println s!"Head = {head}"
  let toomuch := 8 - (numbits - 1) % 8
  --IO.println s!"Bits overhead = {toomuch}"
  let overhead := 2^toomuch
  --IO.println s!"Overhead = {overhead}"
  let newhead := head / overhead
  --IO.println s!"Head sample = {newhead}"
  let mut rnat : Nat := newhead
  for b in rbytes.toList.drop 1 do
    rnat := rnat * 2^8 + b.toNat
  return rnat



def main : IO Unit := do
  -- for i in [0:1000] do
  --   IO.println s!"{i} -> {numBits i}"
  -- let choice := 2050
  -- for _ in [:10000] do
  --   IO.println s!"{← foo choice}"
  let x : Nat := 100000000000000000000
  let y : Nat := 9223372036854775807
  IO.println s!"{x / y} {x % y} {10 * y + x % y}"
