import Lake
open Lake DSL

package «sampcert» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git
  "https://github.com/leanprover-community/aesop.git"

@[default_target]
lean_lib «SampCert» where
  -- add any library configuration options here
