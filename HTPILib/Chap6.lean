/- Copyright 2023 Daniel J. Velleman -/

import HTPILib.Chap8Part1
namespace HTPI

/- Definitions and theorems in Chap8Part1 and HTPIDefs

theorem zero_elts_iff_empty {A : Type} (X : Set A) :
    numElts X 0 ↔ empty X

theorem one_elt_iff_singleton {A : Type} (X : Set A) :
    numElts X 1 ↔ ∃ (x : A), X = {x}

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n

def sum_seq {A : Type} [AddZeroClass A] (m k : Nat) (f : Nat → A) : A :=
  match m with
    | 0 => 0
    | n + 1 => sum_seq n k f + f (k + n)

theorem sum_base {A : Type} [AddZeroClass A] {k : Nat} {f : Nat → A} :
    Sum i from k to k, f i = f k

theorem sum_step {A : Type} [AddZeroClass A] {k n : Nat} {f : Nat → A}
    (h : k ≤ n) : Sum i from k to (n + 1), f i = (Sum i from k to n, f i) + f (n + 1)

theorem sum_from_zero_step {A : Type} [AddZeroClass A] {n : Nat} {f : Nat → A} :
    Sum i from 0 to (n + 1), f i = (Sum i from 0 to n, f i) + f (n + 1)
-/

/- Definitions -/
def nat_even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

def nat_odd (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k + 1

def extendPO {A : Type} (R : BinRel A) (b : A) (x y : A) : Prop :=
  R x y ∨ (R x b ∧ ¬R y b)

def fact (k : Nat) : Nat :=
  match k with
    | 0 => 1
    | n + 1 => (n + 1) * fact n

def Fib (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | k + 2 => Fib k + Fib (k + 1)

def rep_image {A : Type} (f : A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => image f (rep_image f k B)

def cumul_image {A : Type} (f : A → A) (B : Set A) : Set A :=
  { x : A | ∃ (n : Nat), x ∈ rep_image f n B }

/- Section 6.1 -/
theorem Like_Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 + 2 * n := by
  by_induc
  · -- Base Case
    define         --Goal : ∃ (c : Nat), 0 ^ 3 + 2 * 0 = 3 * c
    apply Exists.intro 0
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : 3 ∣ n ^ 3 + 2 * n
    define at ih   --ih : ∃ (c : Nat), n ^ 3 + 2 * n = 3 * c
    obtain (k : Nat) (h1 : n ^ 3 + 2 * n = 3 * k) from ih
    define         --Goal : ∃ (c : Nat), (n + 1) ^ 3 + 2 * (n + 1) = 3 * c
    apply Exists.intro (k + n ^ 2 + n + 1)
    show (n + 1) ^ 3 + 2 * (n + 1) = 3 * (k + n ^ 2 + n + 1) from
      calc (n + 1) ^ 3 + 2 * (n + 1)
        _ = n ^ 3 + 2 * n + 3 * n ^ 2 + 3 * n + 3 := by ring
        _ = 3 * k + 3 * n ^ 2 + 3 * n + 3 := by rw [h1]
        _ = 3 * (k + n ^ 2 + n + 1) := by ring
    done
  done

theorem Like_Example_6_1_1 :
    ∀ (n : Nat), (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1) := by
  by_induc
  · -- Base Case
    rewrite [sum_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1)
    show (Sum i from 0 to n + 1, 2 ^ i) + 1 = 2 ^ (n + 1 + 1) from
      calc (Sum i from 0 to n + 1, 2 ^ i) + 1
        _ = (Sum i from 0 to n, 2 ^ i) + 2 ^ (n + 1) + 1 := by
              rw [sum_from_zero_step]
        _ = (Sum i from 0 to n, 2 ^ i) + 1 + 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
        _ = 2 ^ (n + 1 + 1) := by ring
    done
  done

theorem Example_6_1_3 : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  by_induc
  · -- Base Case
    norm_num
    done
  · -- Induction Step
    fix n : Nat
    assume h1 : n ≥ 5
    assume ih : 2 ^ n > n ^ 2
    have h2 : n * n ≥ 5 * n := Nat.mul_le_mul_right n h1
    show 2 ^ (n + 1) > (n + 1) ^ 2 from
      calc 2 ^ (n + 1)
        _ = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 2 := by linarith
        _ ≥ n ^ 2 + 5 * n := by linarith
        _ > n ^ 2 + 2 * n + 1 := by linarith
        _ = (n + 1) ^ 2 := by ring
    done
  done

#eval 2 - 3       --Answer: 0

theorem Example_6_1_1 :
    ∀ (n : Nat), Sum i from 0 to n, (2 : Int) ^ i =
    (2 : Int) ^ (n + 1) - (1 : Int) := by
  by_induc
  · -- Base Case
    rewrite [sum_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : Sum i from 0 to n, (2 : Int) ^ i =
        (2 : Int) ^ (n + 1) - (1 : Int)
    show Sum i from 0 to n + 1, (2 : Int) ^ i =
        (2 : Int) ^ (n + 1 + 1) - (1 : Int) from
      calc Sum i from 0 to n + 1, (2 : Int) ^ i
        _ = (Sum i from 0 to n, (2 : Int) ^ i)
            + (2 : Int) ^ (n + 1) := by rw [sum_from_zero_step]
        _ = (2 : Int) ^ (n + 1) - (1 : Int)
            + (2 : Int) ^ (n + 1) := by rw [ih]
        _ = (2 : Int) ^ (n + 1 + 1) - (1 : Int) := by ring
    done
  done

/- Section 6.2 -/
lemma Lemma_6_2_1_1 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : R b c) : minimalElt R b B := by
  define at h3
    --h3 : c ∈ B \ {b} ∧ ¬∃ (x : A), x ∈ B \ {b} ∧ R x c ∧ x ≠ c
  define  --Goal : b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  apply And.intro h2    --Goal : ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  contradict h3.right with h5
  obtain (x : A) (h6 : x ∈ B ∧ R x b ∧ x ≠ b) from h5
  apply Exists.intro x  --Goal : x ∈ B \ {b} ∧ R x c ∧ x ≠ c
  apply And.intro
  · -- Proof that x ∈ B \ {b}
    show x ∈ B \ {b} from And.intro h6.left h6.right.right
    done
  · -- Proof that R x c ∧ x ≠ c
    have Rtrans : transitive R := h1.right.left
    have h7 : R x c := Rtrans x b c h6.right.left h4
    apply And.intro h7
    by_contra h8
    rewrite [h8] at h6  --h6 : c ∈ B ∧ R c b ∧ c ≠ b
    have Rantisymm : antisymmetric R := h1.right.right
    have h9 : c = b := Rantisymm c b h6.right.left h4
    show False from h6.right.right h9
    done
  done

lemma Lemma_6_2_1_2 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := sorry

theorem Example_6_2_1 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ n ≥ 1, ∀ (B : Set A), numElts B n →
      ∃ (x : A), minimalElt R x B := by
  by_induc
  · -- Base Case
    fix B : Set A
    assume h2 : numElts B 1
    rewrite [one_elt_iff_singleton] at h2
    obtain (b : A) (h3 : B = {b}) from h2
    apply Exists.intro b
    define         --Goal : b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
    apply And.intro
    · -- Proof that b ∈ B
      rewrite [h3]    --Goal : b ∈ {b}
      define          --Goal : b = b
      rfl
      done
    · -- Proof that nothing in B is smaller than b
      by_contra h4
      obtain (x : A) (h5 : x ∈ B ∧ R x b ∧ x ≠ b) from h4
      have h6 : x ∈ B := h5.left
      rewrite [h3] at h6   --h6 : x ∈ {b}
      define at h6         --h6 : x = b
      show False from h5.right.right h6
      done
    done
  · -- Induction Step
    fix n : Nat
    assume h2 : n ≥ 1
    assume ih : ∀ (B : Set A), numElts B n → ∃ (x : A), minimalElt R x B
    fix B : Set A
    assume h3 : numElts B (n + 1)
    have h4 : n + 1 > 0 := by linarith
    obtain (b : A) (h5 : b ∈ B) from nonempty_of_pos_numElts h3 h4
    set B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h3 h5
    obtain (c : A) (h7 : minimalElt R c B') from ih B' h6
    by_cases h8 : R b c
    · -- Case 1. h8 : R b c
      have h9 : minimalElt R b B := Lemma_6_2_1_1 h h5 h7 h8
      show ∃ (x : A), minimalElt R x B from Exists.intro b h9
      done
    · -- Case 2. h8 : ¬R b c
      have h9 : minimalElt R c B := Lemma_6_2_1_2 h h5 h7 h8
      show ∃ (x : A), minimalElt R x B from Exists.intro c h9
      done
    done
  done

lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := sorry

lemma extendPO_is_trans {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := sorry

lemma extendPO_is_antisymm {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := sorry

lemma extendPO_is_po {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : partial_order (extendPO R b) := 
  And.intro (extendPO_is_ref R b h)
    (And.intro (extendPO_is_trans R b h) (extendPO_is_antisymm R b h))

lemma extendPO_extends {A : Type} (R : BinRel A) (b : A) (x y : A) :
    R x y → extendPO R b x y := by
  assume h1 : R x y
  define
  show R x y ∨ R x b ∧ ¬R y b from Or.inl h1
  done

lemma extendPO_all_comp {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) :
    ∀ (x : A), extendPO R b b x ∨ extendPO R b x b := by
  have Rref : reflexive R := h.left
  fix x : A
  or_left with h1
  define at h1     --h1 : ¬(R x b ∨ R x b ∧ ¬R b b)
  demorgan at h1   --h1 : ¬R x b ∧ ¬(R x b ∧ ¬R b b)
  define           --Goal : R b x ∨ R b b ∧ ¬R x b
  apply Or.inr
  show R b b ∧ ¬R x b from And.intro (Rref b) h1.left
  done

theorem Exercise_6_2_2 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ (n : Nat) (B : Set A), numElts B n → ∃ (T : BinRel A),
    partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
    ∀ x ∈ B, ∀ (y : A), T x y ∨ T y x := by
  by_induc
  · -- Base Case
    fix B : Set A
    assume h2 : numElts B 0
    rewrite [zero_elts_iff_empty] at h2
    define at h2       --h2 : ¬∃ (x : A), x ∈ B
    apply Exists.intro R
    apply And.intro h
    apply And.intro
    · -- Proof that R extends R
      fix x : A; fix y : A
      assume h3 : R x y
      show R x y from h3
      done
    · -- Proof that everything in B comparable to everything under R
      fix x : A
      assume h3 : x ∈ B
      contradict h2
      show ∃ (x : A), x ∈ B from Exists.intro x h3
      done
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (B : Set A), numElts B n → ∃ (T : BinRel A),
      partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B → ∀ (y : A), T x y ∨ T y x
    fix B : Set A
    assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    obtain (b : A) (h4 : b ∈ B) from nonempty_of_pos_numElts h2 h3
    set B' : Set A := B \ {b}
    have h5 : numElts B' n := remove_one_numElts h2 h4
    have h6 : ∃ (T : BinRel A), partial_order T ∧
      (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T x y ∨ T y x := ih B' h5
    obtain (T' : BinRel A)
      (h7 : partial_order T' ∧ (∀ (x y : A), R x y → T' x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T' x y ∨ T' y x) from h6
    have T'po : partial_order T' := h7.left
    have T'extR : ∀ (x y : A), R x y → T' x y := h7.right.left
    have T'compB' : ∀ (x : A), x ∈ B' →
      ∀ (y : A), T' x y ∨ T' y x := h7.right.right
    set T : BinRel A := extendPO T' b
    apply Exists.intro T
    apply And.intro (extendPO_is_po T' b T'po)
    apply And.intro
    · -- Proof that T extends R
      fix x : A; fix y : A
      assume h8 : R x y
      have h9 : T' x y := T'extR x y h8
      show T x y from (extendPO_extends T' b x y h9)
      done
    · -- Proof that everything in B comparable to everything under T
      fix x : A
      assume h8 : x ∈ B
      by_cases h9 : x = b
      · -- Case 1. h9 : x = b
        rewrite [h9]
        show ∀ (y : A), T b y ∨ T y b from extendPO_all_comp T' b T'po
        done
      · -- Case 2. h9 : x ≠ b
        have h10 : x ∈ B' := And.intro h8 h9
        fix y : A
        have h11 : T' x y ∨ T' y x := T'compB' x h10 y
        by_cases on h11
        · -- Case 2.1. h11 : T' x y
          show T x y ∨ T y x from
            Or.inl (extendPO_extends T' b x y h11)
          done
        · -- Case 2.2. h11 : T' y x
          show T x y ∨ T y x from
            Or.inr (extendPO_extends T' b y x h11)
          done
        done
      done
    done
  done

/- Section 6.3 -/
#eval fact 4       --Answer: 24

theorem Example_6_3_1 : ∀ n ≥ 4, fact n > 2 ^ n := by
  by_induc
  · -- Base Case
    norm_num
    done
  · -- Induction Step
    fix n : Nat
    assume h1 : n ≥ 4
    assume ih : fact n > 2 ^ n
    have h2 : n + 1 > 2 := by linarith
    show fact (n + 1) > 2 ^ (n + 1) from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ > (n + 1) * 2 ^ n := by rel [ih]
        _ > 2 * 2 ^ n := by rel [h2]
        _ = 2 ^ (n + 1) := by ring
    done
  done

theorem Example_6_3_2_cheating : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Real; fix m : Nat; fix n : Nat
  ring
  done

theorem Example_6_3_2 : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Real; fix m : Nat
    --Goal : ∀ (n : Nat), a ^ (m + n) = a ^ m * a ^ n
  by_induc
  · -- Base Case
    show a ^ (m + 0) = a ^ m * a ^ 0 from
      calc a ^ (m + 0)
        _ = a ^ m := by rfl
        _ = a ^ m * 1 := (mul_one (a ^ m)).symm
        _ = a ^ m * a ^ 0 := by rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : a ^ (m + n) = a ^ m * a ^ n
    show a ^ (m + (n + 1)) = a ^ m * a ^ (n + 1) from
      calc a ^ (m + (n + 1))
        _ = a ^ ((m + n) + 1) := by rw [add_assoc]
        _ = a * a ^ (m + n) := by rfl
        _ = a * (a ^ m * a ^ n) := by rw [ih]
        _ = a ^ m * (a * a ^ n) := by
              rw [←mul_assoc, mul_comm a, mul_assoc]
        _ = a ^ m * (a ^ (n + 1)) := by rfl
    done
  done

theorem Example_6_3_4 : ∀ (x : Real), x > -1 →
    ∀ (n : Nat), (1 + x) ^ n ≥ 1 + n * x := by
  fix x : Real
  assume h1 : x > -1
  by_induc
  · -- Base Case
    rewrite [Nat.cast_zero]
    linarith
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (1 + x) ^ n ≥ 1 + n * x
    rewrite [Nat.cast_succ]
    have h2 : 0 ≤ 1 + x := by linarith
    have h3 : x ^ 2 ≥ 0 := sq_nonneg x
    have h4 : n * x ^ 2 ≥ 0 :=
      calc n * x ^ 2
        _ ≥ n * 0 := by rel [h3]
        _ = 0 := by ring
    show (1 + x) ^ (n + 1) ≥ 1 + (n + 1) * x from
      calc (1 + x) ^ (n + 1)
        _ = (1 + x) * (1 + x) ^ n := by rfl
        _ ≥ (1 + x) * (1 + n * x) := by rel [ih]
        _ = 1 + x + n * x + n * x ^ 2 := by ring
        _ ≥ 1 + x + n * x + 0 := by rel [h4]
        _ = 1 + (n + 1) * x := by ring
    done
  done

/- Section 6.4 -/
theorem Example_6_4_1 : ∀ m > 0, ∀ (n : Nat),
    ∃ (q r : Nat), n = m * q + r ∧ r < m := by
  fix m : Nat
  assume h1 : m > 0
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, ∃ (q r : Nat), n_1 = m * q + r ∧ r < m
  by_cases h2 : n < m
  · -- Case 1. h2 : n < m
    apply Exists.intro 0
    apply Exists.intro n     --Goal : n = m * 0 + n ∧ n < m
    apply And.intro _ h2
    ring
    done
  · -- Case 2. h2 : ¬n < m
    have h3 : m ≤ n := by linarith
    obtain (k : Nat) (h4 : n = k + m) from Nat.exists_eq_add_of_le' h3
    have h5 : k < n := by linarith
    have h6 : ∃ (q r : Nat), k = m * q + r ∧ r < m := ih k h5
    obtain (q' : Nat)
      (h7 : ∃ (r : Nat), k = m * q' + r ∧ r < m) from h6
    obtain (r' : Nat) (h8 : k = m * q' + r' ∧ r' < m) from h7
    apply Exists.intro (q' + 1)
    apply Exists.intro r'     --Goal : n = m * (q' + 1) + r' ∧ r' < m
    apply And.intro _ h8.right
    show n = m * (q' + 1) + r' from
      calc n
        _ = k + m := h4
        _ = m * q' + r' + m := by rw [h8.left]
        _ = m * (q' + 1) + r' := by ring
    done
  done

lemma exists_eq_add_one_of_ne_zero {n : Nat}
    (h1 : n ≠ 0) : ∃ (k : Nat), n = k + 1 := by
  have h2 : 1 ≤ n := Nat.pos_of_ne_zero h1
  show ∃ (k : Nat), n = k + 1 from Nat.exists_eq_add_of_le' h2
  done

theorem exists_eq_add_two_of_ne_zero_one {n : Nat}
    (h1 : n ≠ 0) (h2 : n ≠ 1) : ∃ (k : Nat), n = k + 2 := by
  have h3 : 1 ≤ n := Nat.pos_of_ne_zero h1
  have h4 : 2 ≤ n := lt_of_le_of_ne' h3 h2
  show ∃ (k : Nat), n = k + 2 from Nat.exists_eq_add_of_le' h4
  done

example : ∀ (n : Nat), Fib n < 2 ^ n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n → Fib n_1 < 2 ^ n_1
  by_cases h1 : n = 0
  · -- Case 1. h1 : n = 0
    rewrite [h1]   --Goal : Fib 0 < 2 ^ 0
    norm_num
    done
  · -- Case 2. h1 : ¬n = 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2 : n = 1
      rewrite [h2]
      norm_num
      done
    · -- Case 2.2. h2 : ¬n = 1
      obtain (k : Nat) (h3 : n = k + 2) from
        exists_eq_add_two_of_ne_zero_one h1 h2
      have h4 : k < n := by linarith
      have h5 : Fib k < 2 ^ k := ih k h4
      have h6 : k + 1 < n := by linarith
      have h7 : Fib (k + 1) < 2 ^ (k + 1) := ih (k + 1) h6
      rewrite [h3]            --Goal : Fib (k + 2) < 2 ^ (k + 2)
      show Fib (k + 2) < 2 ^ (k + 2) from
        calc Fib (k + 2)
          _ = Fib k + Fib (k + 1) := by rfl
          _ < 2 ^ k + Fib (k + 1) := by rel [h5]
          _ < 2 ^ k + 2 ^ (k + 1) := by rel [h7]
          _ ≤ 2 ^ k + 2 ^ (k + 1) + 2 ^ k := by linarith
          _ = 2 ^ (k + 2) := by ring
      done
    done
  done

theorem well_ord_princ (S : Set Nat) : (∃ (n : Nat), n ∈ S) →
    ∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m := by
  contrapos
  assume h1 : ¬∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m
  quant_neg                   --Goal : ∀ (n : Nat), ¬n ∈ S
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n → ¬n_1 ∈ S  --Goal : ¬n ∈ S
  contradict h1 with h2       --h2 : n ∈ S
    --Goal : ∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m
  apply Exists.intro n
  apply And.intro h2          --Goal : ∀ (m : Nat), m ∈ S → n ≤ m
  fix m : Nat
  assume h3 : m ∈ S
  have h4 : m < n → ¬m ∈ S := ih m
  contrapos at h4             --h4 : m ∈ S → ¬m < n
  have h5 : ¬m < n := h4 h3
  linarith
  done

lemma sq_even_iff_even (n : Nat) : nat_even (n * n) ↔ nat_even n := sorry

theorem Theorem_6_4_5 :
    ¬∃ (q p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 := by
  set S : Set Nat :=
    { q : Nat | ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 }
  by_contra h1
  have h2 : ∃ (q : Nat), q ∈ S := h1
  have h3 : ∃ (q : Nat), q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r :=
    well_ord_princ S h2
  obtain (q : Nat) (h4 : q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r) from h3
  have qinS : q ∈ S := h4.left
  have qleast : ∀ (r : ℕ), r ∈ S → q ≤ r := h4.right
  define at qinS     --qinS : ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0
  obtain (p : Nat) (h5 : p * p = 2 * (q * q) ∧ q ≠ 0) from qinS
  have pqsqrt2 : p * p = 2 * (q * q) := h5.left
  have qne0 : q ≠ 0 := h5.right
  have h6 : nat_even (p * p) := Exists.intro (q * q) pqsqrt2
  rewrite [sq_even_iff_even p] at h6    --h6 : nat_even p
  obtain (p' : Nat) (p'halfp : p = 2 * p') from h6
  have h7 : 2 * (2 * (p' * p')) = 2 * (q * q) := by
    rewrite [←pqsqrt2, p'halfp]
    ring
    done
  have h8 : 2 > 0 := by norm_num
  rewrite [mul_left_cancel_iff_of_pos h8] at h7
    --h7 : 2 * (p' * p') = q * q
  have h9 : nat_even (q * q) := Exists.intro (p' * p') h7.symm
  rewrite [sq_even_iff_even q] at h9   --h9 : nat_even q
  obtain (q' : Nat) (q'halfq : q = 2 * q') from h9
  have h10 : 2 * (p' * p') = 2 * (2 * (q' * q')) := by
    rewrite [h7, q'halfq]
    ring
    done
  rewrite [mul_left_cancel_iff_of_pos h8] at h10
    --h10 : p' * p' = 2 * (q' * q')
  have q'ne0 : q' ≠ 0 := by
    contradict qne0 with h11
    rewrite [q'halfq, h11]
    rfl
    done
  have q'inS : q' ∈ S := Exists.intro p' (And.intro h10 q'ne0)
  have qleq' : q ≤ q' := qleast q' q'inS
  rewrite [q'halfq] at qleq'        --qleq' : 2 * q' ≤ q'
  contradict q'ne0
  linarith
  done

/- Section 6.5 -/
theorem rep_image_base {A : Type} (f : A → A) (B : Set A) :
    rep_image f 0 B = B := by rfl

theorem rep_image_step {A : Type} (f : A → A) (n : Nat) (B : Set A) :
    rep_image f (n + 1) B = image f (rep_image f n B) := by rfl

lemma rep_image_sub_closed {A : Type} {f : A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed f D) :
    ∀ (n : Nat), rep_image f n B ⊆ D := by
  by_induc
  · -- Base Case
    rewrite [rep_image_base]          --Goal : B ⊆ D
    show B ⊆ D from h1
    done
  · -- Induction Step
    fix n : Nat
    assume ih : rep_image f n B ⊆ D   --Goal : rep_image f (n + 1) B ⊆ D
    fix x : A
    assume h3 : x ∈ rep_image f (n + 1) B  --Goal : x ∈ D
    rewrite [rep_image_step] at h3
    define at h3    --h3 : ∃ (x_1 : A), x_1 ∈ rep_image f n B ∧ f x_1 = x
    obtain (b : A) (h4 : b ∈ rep_image f n B ∧ f b = x) from h3
    rewrite [←h4.right]   --Goal : f b ∈ D    
    have h5 : b ∈ D := ih h4.left
    define at h2          --h2 : ∀ (x : A), x ∈ D → f x ∈ D
    show f b ∈ D from h2 b h5
    done
  done

theorem Theorem_6_5_1 {A : Type} (f : A → A) (B : Set A) :
    closure f B (cumul_image f B) := by
  define
  apply And.intro
  · -- Proof that cumul_image f B ∈ { D : Set A | B ⊆ D ∧ closed f D }
    define  --Goal : B ⊆ cumul_image f B ∧ closed f (cumul_image f B)
    apply And.intro
    · -- Proof that B ⊆ cumul_image f B
      fix x : A
      assume h1 : x ∈ B
      define     --Goal : ∃ (n : Nat), x ∈ rep_image f n B
      apply Exists.intro 0
      rewrite [rep_image_base]  --Goal : x ∈ B
      show x ∈ B from h1
      done
    · -- Proof that cumul_image f B closed under f
      define
      fix x : A
      assume h1 : x ∈ cumul_image f B  --Goal : f x ∈ cumul_image f B
      define at h1
      obtain (m : Nat) (h2 : x ∈ rep_image f m B) from h1
      define     --Goal : ∃ (n : Nat), f x ∈ rep_image f n B
      apply Exists.intro (m + 1) --Goal : f x ∈ rep_image f (m + 1) B
      rewrite [rep_image_step]   --Goal : f x ∈ image f (rep_image f m B)
      define     --Goal : ∃ (x_1 : A), x_1 ∈ rep_image f m B ∧ f x_1 = f x
      apply Exists.intro x  --Goal : x ∈ rep_image f m B ∧ f x = f x
      apply And.intro h2
      rfl
      done
    done
  · -- Proof that cumul_image f B is smallest
    fix D : Set A
    assume h1 : D ∈ { D : Set A | B ⊆ D ∧ closed f D }
    define at h1  --h1 : B ⊆ D ∧ closed f D
    define   --Goal : ∀ ⦃a : A⦄, a ∈ cumul_image f B → a ∈ D
    fix x : A
    assume h2 : x ∈ cumul_image f B  --Goal : x ∈ D
    define at h2  --h2: ∃ (n : Nat), x ∈ rep_image f n B
    obtain (m : Nat) (h3 : x ∈ rep_image f m B) from h2
    have h4 : rep_image f m B ⊆ D :=
      rep_image_sub_closed h1.left h1.right m
    show x ∈ D from h4 h3
    done
  done