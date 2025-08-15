import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties
import SampCert.DifferentialPrivacy.Generic

namespace SLang

def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd

  /- This is the Shuffle Model. -/
def RRShuffle(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

#check Shuffler
#check RandomizedResponse.RRSample
#check Mechanism

def UniformShuffler {U: Type}[BEq U](f: List U → SLang (List U)) : Prop :=
  ∀ l₁ l₂: List U, f l₁ l₂ = if List.isPerm l₁ l₂ then (1: ENNReal)/(l₁.length.factorial) else (0: ENNReal)

lemma UniformShuffler_norms {U: Type}[DecidableEq U][BEq U](f: List U → SLang (List U)) (h:UniformShuffler f)
:∀(b: List U),∑' (i : List U), f b i = 1 := by
  intro b
  have h2 :∀ x i: List U, f x i  = (if List.isPerm x i then  (1: ENNReal)/(x.length.factorial) else (0: ENNReal)) := by
    unfold UniformShuffler at h
    exact h
  conv =>
    enter [1,1,i]
    rw [h2]

  rw [← @ENNRealLemmas.tsum_ite_mult]
  conv =>
    enter [1]
    rw[ENNReal.tsum_mul_left]
  sorry




def ShuffleAlgorithm [BEq U](m : List T → SLang (List U))(f : List U → SLang (List U))(_: UniformShuffler f)(l: List T) := do
  let x ← m l
  let b ← f x
  return b

lemma ShuffleAlgorithm_norms {U: Type} [BEq U] (m : Mechanism T (List U))(f : List U → SLang (List U))(h: UniformShuffler f)(l: List T):
HasSum (ShuffleAlgorithm (fun x => (m x).1) f h l) 1  := by
  unfold ShuffleAlgorithm
  simp_all only [bind, pure, bind_pure]
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1,1,b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    apply UniformShuffler_norms
    exact h
  simp
  rw [← Summable.hasSum_iff ENNReal.summable]
  exact (m l).2

def ShuffleAlgorithm_PMF {U: Type}[BEq U] (m : Mechanism T (List U ))(f : List U → SLang (List U))(h: UniformShuffler f)(l: List T) : PMF (List U) :=
  ⟨ShuffleAlgorithm (fun x => (m x).1) f h l, ShuffleAlgorithm_norms m f h l⟩

theorem ShuffleAlgorithm_is_DP [BEq U](m : Mechanism T (List U))(f : List U → SLang (List U))(ε : ℝ)(hdp: DP_withUpdateNeighbour m ε)
(hsa: UniformShuffler f → True): DP_withUpdateNeighbour (ShuffleAlgorithm_PMF m f hsa) ε := by sorry

def BinomialSample (seed: MultiBernoulli.SeedType)(n:PNat) := do
  let seeds := List.replicate n seed
  let list ← MultiBernoulli.MultiBernoulliSample (seeds)
  let k := List.count true list
  return k
