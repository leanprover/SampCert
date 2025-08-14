import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties

namespace SLang


def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd
#check Shuffler

def BinomialSample (seed: MultiBernoulli.SeedType)(n:PNat) := do
  let seeds := List.replicate n seed
  let list ← MultiBernoulli.MultiBernoulliSample (seeds)
  let k := List.count true list
  return k

theorem BinomialSample_norms [LawfulMonad SLang] (seed : MultiBernoulli.SeedType) (n : PNat) :
  HasSum (BinomialSample seed n) 1 := by
  rw [BinomialSample]
  simp
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  have h: (push_forward (MultiBernoulli.MultiBernoulliSample (List.replicate (↑n) seed))
        (fun (a : List Bool) => (List.count true a))) = (fun (b : Nat) =>
        (∑' (a : List Bool), if b = List.count true a then MultiBernoulli.MultiBernoulliSample
        (List.replicate (↑n) seed) a else 0)) := by
          unfold push_forward
          rfl
  rw [← h]
  rw [push_forward_prob_is_prob]
  simp [MultiBernoulli.MultiBernoulliSample_normalizes]

theorem BinomialSample_kprob (seed: MultiBernoulli.SeedType) (n : PNat) (k : Nat) :
  BinomialSample seed n k = ((n: Nat).choose k) * ((num / den) ^ k) * ((1 - (num / den)) ^ (n - k)) := by
  rw[BinomialSample]
  simp
  unfold MultiBernoulli.MultiBernoulliSample
  simp [pure, bind]

  sorry
