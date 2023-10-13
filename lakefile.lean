import Lake
open Lake DSL

package htpi {
  moreServerArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-Dpp.funBinderTypes=true"  -- shows types of bound variables
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "2df6bb4167844ead7631ba547d6a44d465c0b37b"

@[default_target]
lean_lib HTPILib {
  moreLeanArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-Dpp.funBinderTypes=true"  -- shows types of bound variables
  ]
}
