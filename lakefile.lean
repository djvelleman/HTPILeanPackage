import Lake
open Lake DSL

package hTPI {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[defaultTarget]
lean_lib HTPI {
  -- add library configuration options here
  srcDir := "HTPILib"
  roots := #[`HTPIDefs]
}

