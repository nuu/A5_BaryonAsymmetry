import Lake
open Lake DSL

package A5Baryon where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib A5Baryon where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
