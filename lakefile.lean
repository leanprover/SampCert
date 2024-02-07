import Lake
open Lake DSL

package «sampcert» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"1bda3b46774ca7d204e632781b92c31e32828e89"

@[default_target]
lean_lib «SampCert» where
  -- add any library configuration options here
