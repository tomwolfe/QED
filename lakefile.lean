import Lake
open Lake DSL

package QED where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib QED where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
