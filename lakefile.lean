import Lake
open Lake DSL

package «mirror» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"1bda3b46774ca7d204e632781b92c31e32828e89"

require kolmogorov_extension4 from git
  "https://github.com/RemyDegenne/kolmogorov_extension4.git"@"183d5b2dfa9ab01c5b22d7ebf69112aa73df2727"

--  "/Users/trjohnb/Code/kolmogorov_extension4"

@[default_target]
lean_lib «Mirror» where
  -- add any library configuration options here
