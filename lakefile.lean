import Lake
open Lake DSL

package QED where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib QED where
  srcDir := "."

lean_lib Compartmental where
  srcDir := "."

lean_lib VeriTrialExport where
  srcDir := "."

-- Pinned to the release tag matching lean-toolchain, not "master".
-- "master" floats, and the commit it resolved to (810b3888) requires
-- leanprover/lean4:v4.34.0-rc2, whose `lake` binary SIGTRAPs on arm64 Darwin 27
-- (exit 133) on every invocation. The toolchain is pinned instead, and mathlib
-- follows it, so the pair is known-good together.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"
