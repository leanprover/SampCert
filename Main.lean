import SampCert
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Bernoulli.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code
import SampCert.Samplers.LaplaceGen.Code
import SampCert.Samplers.Geometric.Code
import SampCert.Samplers.Gaussian.Code
import SampCert.Samplers.GaussianGen.Code

open SLang Std

def comp (n : ℕ+) : SLang ℕ := do
  let x ← UniformPowerOfTwoSample n
  return x + 1

def double (n : ℕ+) : SLang (ℕ × ℕ) := do
  let x ← UniformPowerOfTwoSample n
  let y ← UniformPowerOfTwoSample n
  return (x,y)

def main : IO Unit := do

  let sampleSize : ℕ := 10
  let sampleNum : ℕ := 1000

  let mut arr : Array ℕ := Array.mkArray (sampleSize) 0
  for _ in [:sampleNum] do
    let r ← run <| UniformPowerOfTwoSample ⟨ sampleSize , by aesop ⟩
    let v := arr[r]!
    arr := arr.set! r (v + 1)

  let mut res : Array Float := Array.mkArray (sampleSize) 0.0
  for i in [:sampleSize] do
    let total : Float := arr[i]!.toFloat
    let freq : Float := total / sampleNum.toFloat
    res := res.set! i freq

  IO.println s!"Repeated uniform sampling: {res}"

  let mut arr2 : Array ℕ := Array.mkArray (sampleSize) 0
  for _ in [:sampleNum] do
    let r ← run <| probWhile (fun x => x % 2 == 0) (fun _ => UniformPowerOfTwoSample ⟨ sampleSize , by aesop ⟩) 0
    let v := arr2[r]!
    arr2 := arr2.set! r (v + 1)

  let mut res2 : Array Float := Array.mkArray (sampleSize) 0.0
  for i in [:sampleSize] do
    let total : Float := arr2[i]!.toFloat
    let freq : Float := total / sampleNum.toFloat
    res2 := res2.set! i freq

  IO.println s!"Repeated uniform sampling with filtering: {res2}"

  let mut arr3 : Array ℕ := Array.mkArray (sampleSize) 0
  for _ in [:sampleNum] do
    let r ← run <| probUntil (UniformPowerOfTwoSample ⟨ sampleSize , by aesop ⟩) (fun x => x % 2 == 0)
    let v := arr3[r]!
    arr3 := arr3.set! r (v + 1)

  let mut res3 : Array Float := Array.mkArray (sampleSize) 0.0
  for i in [:sampleSize] do
    let total : Float := arr3[i]!.toFloat
    let freq : Float := total / sampleNum.toFloat
    res3 := res3.set! i freq

  IO.println s!"Repeated uniform sampling with filtering: {res3}"

  let u : ℕ ← run <| UniformSample 5
  IO.println s!"**1 Uniform sample: {u}"

  let u : ℕ ← run <| UniformSample 10
  IO.println s!"**2 Uniform sample: {u}"

  let u : ℕ ← run <| UniformSample 20
  IO.println s!"**3 Uniform sample: {u}"

  let u : ℕ ← run <| UniformSample 15
  IO.println s!"**4 Uniform sample: {u}"

  let u : ℕ × ℕ ← run <| double 15
  IO.println s!"**4 Uniform sample: {u}"

  let mut arr4 : Array ℕ := Array.mkArray sampleSize 0
  for _ in [:sampleNum] do
    let r ← run <| UniformSample 10
    let v := arr4[r]!
    arr4 := arr4.set! r (v + 1)

  let mut res4 : Array Float := Array.mkArray sampleSize 0.0
  for i in [:sampleSize] do
    let total : Float := arr4[i]!.toFloat
    let freq : Float := total / sampleNum.toFloat
    res4 := res4.set! i freq

  IO.println s!"Repeated uniform sampling plop: {res3}"

  let u : ℕ ← run <| UniformSample 15
  IO.println s!"**4 Uniform sample: {u}"

  let u : Bool ← run <| BernoulliSample 1 2 (by aesop)
  IO.println s!"Bernoulli sample: {u}"

  let u : Bool ← run <| BernoulliSample 1 100 (by aesop)
  IO.println s!"Bernoulli sample: {u}"

  let u : Bool ← run <| BernoulliExpNegSample 1 2
  IO.println s!"Bernoulli NE sample: {u}"

  let u : ℤ ← run <| DiscreteLaplaceSample 1 1
  IO.println s!"Laplace sample: {u}"

  let u : ℤ ← run <| DiscreteLaplaceGenSample 1 1 10
  IO.println s!"Laplace Gen sample: {u}"

  let u : ℤ ← run <| DiscreteGaussianSample 1 1 7
  IO.println s!"Gaussian sample: {u}"

  let u : ℤ ← run <| DiscreteGaussianGenSample 1 1 10
  IO.println s!"Gaussian Gen sample: {u}"
