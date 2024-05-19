import Lake
open Lake DSL

require mathlib from git
  -- 4.3.0
  "https://github.com/leanprover-community/mathlib4.git"@"753159252c585df6b6aa7c48d2b8828d58388b79"

package «examples» where
  -- add package configuration options here

@[default_target]
lean_lib «Examples» where
  -- add library configuration options here
