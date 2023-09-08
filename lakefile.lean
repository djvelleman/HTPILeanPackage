import Lake
open Lake DSL

package hTPI {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "2df6bb4167844ead7631ba547d6a44d465c0b37b"

@[default_target]
lean_lib HTPI {
  -- add library configuration options here
  srcDir := "HTPILib"
  roots := #[`HTPIDefs, `IntroLean,
    `Chap3, `Chap4, `Chap5, `Chap6, `Chap7, `Chap8Part1, `Chap8Part2]
}
