import Lake
open Lake DSL

package hTPI {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d8c7d9897527e99b28862cdf5a4a13aefee95897"

@[default_target]
lean_lib HTPI {
  -- add library configuration options here
  srcDir := "HTPILib"
  roots := #[`HTPIDefs, `IntroLean,
    `Chap3, `Chap4, `Chap5, `Chap6, `Chap7, `Chap8Part1, `Chap8Part2]
}
