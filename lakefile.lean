import Lake
open Lake DSL

package hTPI {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "100392f8614e94b2dfeca445f535701502a066c3"

@[default_target]
lean_lib HTPI {
  -- add library configuration options here
  srcDir := "HTPILib"
  roots := #[`HTPIDefs, `MathlibTactics,
    `Chap3, `Chap4, `Chap5, `Chap6, `Chap7, `Chap8Part1, `Chap8Part2]
}

