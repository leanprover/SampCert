import Mathlib.Probability.ProbabilityMassFunction.Monad

variable {T}

-- To me the key advantage is not in easing the statements of lemmas
-- about probabilities, but rather in being able to define something
-- like the while combinator in a natural way: if you only allowed for
-- full distributions in your monad, then the while combinator would have
-- to take an extra argument showing somehow that would ensure termination
-- with probability 1

-- Functions are partial, requires the use of dependent types
abbrev M1 T := Pmf T

-- Functions are partial, requires the use of dependent types
-- Annoying: pmf defined on product of value and fuel
-- How to define the combinator?
abbrev M2 T := StateT Nat Pmf T

-- Functions are total
-- Reasoning very difficult because pmf defined on Except
-- Conditioning required to say: prob of coin = true given that it did not fail
abbrev M3 T := StateT Nat (ExceptT String Pmf) T

-- Option represent divergence
-- you need to prove that probability of returning none is 0
-- which means termination wp 1
-- conditioning everywhere
abbrev M4 T := StateT Nat (OptionT Pmf) T


abbrev M5 T := ReaderT Nat (OptionT Pmf) T

lemma test :
