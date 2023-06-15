import Lake
open Lake DSL

package hTPI {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b8c4b6e95c21e1d23f51178abfb951d8b9c1dca9"

@[default_target]
lean_lib HTPI {
  -- add library configuration options here
  srcDir := "HTPILib"
  roots := #[`HTPIDefs, `MathlibTactics,
    `Chap3, `Chap4, `Chap5, `Chap6, `Chap7, `Chap8Part1, `Chap8Part2]
}

