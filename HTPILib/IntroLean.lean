/- Copyright 2023 Daniel J. Velleman -/

import HTPILib.HTPIDefs
namespace HTPI

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  have h4 : Q → R := h h3
  contrapos at h4            --Now h4 : ¬R → ¬Q
  show ¬Q from h4 h2
  done

theorem extremely_easy (P : Prop) (h : P) : P := h

theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos         --Goal is now P → ¬R
  assume h3 : P
  have h4 : Q := h1 h3
  show ¬R from h2 h4
  done
  
theorem Example_3_2_5_simple
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2       --Now h2 : ¬(a ∈ B ∧ ¬a ∈ C)
  demorgan at h2; conditional at h2
                     --Now h2 : a ∈ B → a ∈ C
  show a ∈ C from h2 h1
  done

theorem Example_3_2_5_simple_general
    (U : Type) (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2; conditional at h2
  show a ∈ C from h2 h1
  done