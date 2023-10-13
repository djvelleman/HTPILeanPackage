/- Copyright 2023 Daniel J. Velleman -/

import HTPILib.IntroLean
namespace HTPI

/- Definitions -/
def even (n : Int) : Prop := ∃ (k : Int), n = 2 * k

def odd (n : Int) : Prop := ∃ (k : Int), n = 2 * k + 1

/- Sections 3.1 and 3.2 -/
theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  have h5 : Q → R := h h3
  have h6 : R := h5 h4
  show False from h2 h6
  done

theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  contradict h2
  show R from h h3 h4
  done

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by
  apply h3 _
  define at h2
  demorgan at h2; conditional at h2
  show a ∈ B from h2 h1
  done

/- Section 3.3 -/
example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg     --Goal is now ∀ (x : U), ¬P x
  fix y : U
  have h3 : P y → ¬Q y := h1 y
  have h4 : Q y := h2 y
  contrapos at h3  --Now h3 : Q y → ¬P y
  show ¬P y from h3 h4
  done

example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by
  define  --Goal : ∀ ⦃a : U⦄, a ∈ A → a ∈ C
  fix y : U
  assume h3 : y ∈ A
  have h4 : y ∉ B := h2 y h3
  define at h1  --h1 : ∀ ⦃a : U⦄, a ∈ A → a ∈ B ∪ C
  have h5 : y ∈ B ∪ C := h1 h3
  define at h5  --h5 : y ∈ B ∨ y ∈ C
  conditional at h5  --h5 : ¬y ∈ B → y ∈ C
  show y ∈ C from h5 h4
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (a : U)
    (h3 : ∀ (y : U), P a → Q y) from h2
  have h4 : ∃ (y : U), P a → ¬ Q y := h1 a
  obtain (b : U) (h5 : P a → ¬ Q b) from h4
  have h6 : P a → Q b := h3 b
  apply Exists.intro a _
  by_contra h7
  show False from h5 h7 (h6 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
  assume h1 : ⋃₀ F ⊆ B
  define
  fix x : Set U
  assume h2 : x ∈ F
  define
  fix y : U
  assume h3 : y ∈ x
  define at h1
  apply h1 _
  define
  apply Exists.intro x _
  show x ∈ F ∧ y ∈ x from And.intro h2 h3
  done

/- Section 3.4 -/
theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by
  define
  fix x : U
  assume h3 : x ∈ A ∩ C
  define at h3; define
  apply And.intro
  · -- Proof that x ∈ B.
    show x ∈ B from h1 h3.left
    done
  · -- Proof that ¬x ∈ D.
    contradict h2 with h4
    apply Exists.intro x
    show x ∈ C ∩ D from And.intro h3.right h4
    done
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x ↔ Q x) :
    (∃ (x : U), P x) ↔ ∃ (x : U), Q x := by
  apply Iff.intro
  · -- (→)
    assume h2 : ∃ (x : U), P x
    obtain (u : U) (h3 : P u) from h2
    have h4 : P u ↔ Q u := h1 u
    apply Exists.intro u
    show Q u from h4.ltr h3
    done
  · -- (←)
    assume h2 : ∃ (x : U), Q x
    obtain (u : U) (h3 : Q u) from h2
    show ∃ (x : U), P x from Exists.intro u ((h1 u).rtl h3)
    done
  done

theorem Example_3_4_5 (U : Type)
    (A B C : Set U) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply Set.ext
  fix x : U
  show x ∈ A ∩ (B \ C) ↔ x ∈ (A ∩ B) \ C from
    calc x ∈ A ∩ (B \ C)
      _ ↔ x ∈ A ∧ (x ∈ B ∧ x ∉ C) := Iff.refl _
      _ ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ C := and_assoc.symm
      _ ↔ x ∈ (A ∩ B) \ C := Iff.refl _
  done

/- Section 3.5 -/
theorem Example_3_5_2
    (U : Type) (A B C : Set U) :
    A \ (B \ C) ⊆ (A \ B) ∪ C := by
  fix x : U
  assume h1 : x ∈ A \ (B \ C)
  define; define at h1
  have h2 : ¬x ∈ B \ C := h1.right
  define at h2; demorgan at h2
            --h2 : ¬x ∈ B ∨ x ∈ C
  by_cases on h2
  · -- Case 1. h2 : ¬x ∈ B
    apply Or.inl
    show x ∈ A \ B from And.intro h1.left h2
    done
  · -- Case 2. h2 : x ∈ C
    apply Or.inr
    show x ∈ C from h2
    done
  done

example (U : Type) (A B C : Set U)
    (h1 : A \ B ⊆ C) : A ⊆ B ∪ C := by
  fix x : U
  assume h2 : x ∈ A
  define
  or_right with h3
  show x ∈ C from h1 (And.intro h2 h3)
  done

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  quant_neg at h2
  have h4 : a ∈ B ∪ C := h1 h3
  have h5 : a ∉ A ∩ B := h2 a
  define at h4
  define at h5; demorgan at h5
  disj_syll h5 h3  --h5 : ¬a ∈ B
  disj_syll h4 h5  --h4 : a ∈ C
  show a ∈ C from h4
  done

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  have h4 : a ∈ B ∪ C := h1 h3
  define at h4
  have h5 : a ∉ B := by
    contradict h2 with h6
    show ∃ (x : U), x ∈ A ∩ B from
      Exists.intro a (And.intro h3 h6)
    done
  disj_syll h4 h5  --h4 : a ∈ C
  show a ∈ C from h4
  done

/- Section 3.6 -/
theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ ∅ ∪ B
    define at h1
    have h2 : x ∉ ∅ := by
      by_contra h3
      define at h3  --h3 : False
      show False from h3
      done
    disj_syll h1 h2  --h1 : x ∈ B
    show x ∈ B from h1
    done
  · -- (←)
    assume h1 : x ∈ B
    show x ∈ ∅ ∪ B from Or.inr h1
    done
  done

theorem union_comm {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
  apply Set.ext
  fix x : U
  define : x ∈ X ∪ Y
  define : x ∈ Y ∪ X
  show x ∈ X ∨ x ∈ Y ↔ x ∈ Y ∨ x ∈ X from or_comm
  done

theorem Example_3_6_2 (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U),
    A ∪ B = B := by
  exists_unique
  · -- Existence
    apply Exists.intro ∅
    show ∀ (B : Set U), ∅ ∪ B = B from empty_union
    done
  · -- Uniqueness
    fix C : Set U; fix D : Set U
    assume h1 : ∀ (B : Set U), C ∪ B = B
    assume h2 : ∀ (B : Set U), D ∪ B = B
    have h3 : C ∪ D = D := h1 D
    have h4 : D ∪ C = C := h2 C 
    show C = D from
      calc C
        _ = D ∪ C := h4.symm
        _ = C ∪ D := union_comm D C
        _ = D := h3
    done
  done

theorem Example_3_6_4 (U : Type) (A B C : Set U)
    (h1 : ∃ (x : U), x ∈ A ∩ B)
    (h2 : ∃ (x : U), x ∈ A ∩ C)
    (h3 : ∃! (x : U), x ∈ A) :
    ∃ (x : U), x ∈ B ∩ C := by
  obtain (b : U) (h4 : b ∈ A ∩ B) from h1
  obtain (c : U) (h5 : c ∈ A ∩ C) from h2
  obtain (a : U) (h6 : a ∈ A) (h7 : ∀ (y z : U),
    y ∈ A → z ∈ A → y = z)  from h3
  define at h4; define at h5
  have h8 : b = c := h7 b c h4.left h5.left
  rewrite [h8] at h4
  show ∃ (x : U), x ∈ B ∩ C from
    Exists.intro c (And.intro h4.right h5.right)
  done

/- Section 3.7 -/
theorem Theorem_3_3_7 :
    ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
  fix a : Int; fix b : Int; fix c : Int
  assume h1 : a ∣ b; assume h2 : b ∣ c
  define at h1; define at h2; define
  obtain (m : Int) (h3 : b = a * m) from h1
  obtain (n : Int) (h4 : c = b * n) from h2
  rewrite [h3] at h4   --h4 : c = a * m * n
  apply Exists.intro (m * n)
  rewrite [mul_assoc a m n] at h4
  show c = a * (m * n) from h4
  done

theorem Theorem_3_4_7 :
    ∀ (n : Int), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  fix n : Int
  apply Iff.intro
  · -- (→)
    assume h1 : 6 ∣ n; define at h1
    obtain (k : Int) (h2 : n = 6 * k) from h1
    apply And.intro
    · -- Proof that 2 ∣ n
      define
      apply Exists.intro (3 * k)
      rewrite [←mul_assoc 2 3 k]
      show n = 2 * 3 * k from h2
      done
    · -- Proof that 3 ∣ n
      define
      apply Exists.intro (2 * k)
      rewrite [←mul_assoc 3 2 k]
      show n = 3 * 2 * k from h2
      done
    done
  · -- (←)
    assume h1 : 2 ∣ n ∧ 3 ∣ n
    have h2 : 2 ∣ n := h1.left
    have h3 : 3 ∣ n := h1.right
    define at h2; define at h3; define
    obtain (j : Int) (h4 : n = 2 * j) from h2
    obtain (k : Int) (h5 : n = 3 * k) from h3
    have h6 : 6 * (j - k) = n :=
      calc 6 * (j - k)
        _ = 3 * (2 * j) - 2 * (3 * k) := by ring
        _ = 3 * n - 2 * n := by rw [←h4, ←h5]
        _ = n := by ring
    show ∃ (c : Int), n = 6 * c from
      Exists.intro (j - k) h6.symm
    done
  done

theorem Example_3_5_4 (x : Real) (h1 : x ≤ x ^ 2) : x ≤ 0 ∨ 1 ≤ x := by
  or_right with h2     --h2 : ¬x ≤ 0;  Goal : 1 ≤ x
  have h3 : 0 < x := lt_of_not_le h2
  have h4 : 1 * x ≤ x * x :=
    calc 1 * x
      _ = x := one_mul x
      _ ≤ x ^ 2 := h1
      _ = x * x := by ring
  show 1 ≤ x from le_of_mul_le_mul_right h4 h3
  done