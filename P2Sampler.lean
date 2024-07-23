import Mathlib.Data.Nat.Bits

open BitVec
@[export super_sampler]
def foo (n : Nat) : IO Nat := do
  if n = 0 then
    panic s!"Cannot sample 0 bits"
  -- from least significant to most significant
  let bits := n.bits
  --IO.println s!"Representation = {bits}"
  let want := bits.length - 1
  --IO.println s!"Number of bits I want = {want}"
  let nbytes := want / 8 + 1
  --IO.println s!"Number of requested bytes = {nbytes}"
  let rbytes ← IO.getRandomBytes nbytes.toUSize
  --for b in rbytes do
  --   IO.println s!"{b.toNat.bits}"
  let head := (rbytes.get! 0).toNat
  --IO.println s!"Head = {head}"
  let toomuch := 8 - (bits.length - 1) % 8
  --IO.println s!"Bits overhead = {toomuch}"
  let overhead := 2^toomuch
  --IO.println s!"Overhead = {overhead}"
  let newhead := head / overhead
  --IO.println s!"Head sample = {newhead}"
  let mut rnat : Nat := newhead
  for b in rbytes.toList.drop 1 do
    rnat := rnat * 2^8 + b.toNat
  return rnat
