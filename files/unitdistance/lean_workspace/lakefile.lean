import Lake
open Lake DSL

package «workspace» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from "/cmlscratch/asoltan3/goedel-agent/mathlib4"

@[default_target]
lean_lib «Workspace» where
  globs := #[.submodules `Workspace]
