import FiniteSets  -- includes HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true

/- Definitions from Chapter 4 -/
def Dom {A B : Type} (R : Set (A × B)) : Set A :=
    { a : A | ∃ (b : B), (a, b) ∈ R }

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
    { b : B | ∃ (a : A), (a, b) ∈ R }

def comp {A B C : Type} (S : Set (B × C)) (R : Set (A × B)) :
    Set (A × C) := { (a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S }

def extension {A B : Type} (R : Rel A B) : Set (A × B) :=
    { (a, b) : A × B | R a b }

def reflexive {A : Type} (R : BinRel A) : Prop :=
    ∀ (x : A), R x x

def symmetric {A : Type} (R : BinRel A) : Prop :=
    ∀ (x y : A), R x y → R y x

def transitive {A : Type} (R : BinRel A) : Prop :=
    ∀ (x y z : A), R x y → R y z → R x z

def elementhood (A : Type) (a : A) (X : Set A) : Prop := a ∈ X

def relFromExt {A B : Type}
    (R : Set (A × B)) (a : A) (b : B) : Prop := (a, b) ∈ R

def antisymmetric {A : Type} (R : BinRel A) : Prop :=
    ∀ (x y : A), R x y → R y x → x = y

def partial_order {A : Type} (R : BinRel A) : Prop :=
    reflexive R ∧ transitive R ∧ antisymmetric R

def total_order {A : Type} (R : BinRel A) : Prop :=
    partial_order R ∧ ∀ (x y : A), R x y ∨ R y x

def sub (A : Type) (X Y : Set A) : Prop := X ⊆ Y

def smallestElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
    b ∈ B ∧ ∀ x ∈ B, R b x

def minimalElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
    b ∈ B ∧ ¬∃ x ∈ B, R x b ∧ x ≠ b

def upperBd {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
    ∀ x ∈ B, R x a

def lub {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
    smallestElt R a { c : A | upperBd R c B }

def equiv_rel {A : Type} (R : BinRel A) : Prop :=
    reflexive R ∧ symmetric R ∧ transitive R

def equivClass {A : Type} (R : BinRel A) (x : A) : Set A :=
    { y : A | R y x }

def mod (A : Type) (R : BinRel A) : Set (Set A) :=
    { equivClass R x | x : A }

def pairwise_disjoint {A : Type} (F : Set (Set A)) : Prop :=
    ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → empty (X ∩ Y)

def partition {A : Type} (F : Set (Set A)) : Prop :=
    (∀ (x : A), x ∈ ⋃₀ F) ∧ pairwise_disjoint F ∧ ∀ X ∈ F, ¬empty X

def EqRelFromPart {A : Type} (F : Set (Set A)) (x y : A) : Prop :=
    ∃ X ∈ F, x ∈ X ∧ y ∈ X

/- Definitions from Chapter 5 -/
def onto {A B : Type} (f : A → B) : Prop :=
    ∀ (y : B), ∃ (x : A), f x = y

def one_to_one {A B : Type} (f : A → B) : Prop :=
    ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2

def closed {A : Type} (f : A → A) (C : Set A) : Prop := ∀ x ∈ C, f x ∈ C

def closure {A : Type} (f : A → A) (B C : Set A) : Prop :=
    smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed f D }

def closed2 {A : Type} (f : A → A → A) (C : Set A) : Prop :=
    ∀ x ∈ C, ∀ y ∈ C, f x y ∈ C

def closure2 {A : Type} (f : A → A → A) (B C : Set A) : Prop := 
    smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed2 f D }

def closed_family {A : Type} (F : Set (A → A)) (C : Set A) : Prop :=
    ∀ f ∈ F, closed f C

def closure_family {A : Type} (F : Set (A → A)) (B C : Set A) : Prop :=
    smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed_family F D }

def image {A B : Type} (f : A → B) (X : Set A) : Set B :=
    { f x | x ∈ X }

def inverse_image {A B : Type} (f : A → B) (Y : Set B) : Set A :=
    { a : A | f a ∈ Y }

/- Definitions and theorems in FiniteSets and HTPIDefs
def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
    { (b, a) : B × A | (a, b) ∈ R }

def empty {A : Type} (X : Set A) : Prop := ¬∃ (x : A), x ∈ X 

def graph {A B : Type} (f : A → B) : Set (A × B) :=
    { (a, b) : A × B | f a = b }

def is_func_graph {A B : Type} (G : Set (A × B)) : Prop :=
    ∀ (x : A), ∃! (y : B), (x, y) ∈ G

theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F := by

theorem simp_inv {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

theorem Theorem_4_2_5_1 {A B : Type}
    (R : Set (A × B)) : inv (inv R) = R := by rfl

theorem zero_elts_iff_empty {A : Type} (X : Set A) :
    numElts X 0 ↔ empty X

theorem one_elt_iff_singleton {A : Type} (X : Set A) :
    numElts X 1 ↔ ∃ (x : A), X = {x}

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n

def sum_less {A : Type} [AddZeroClass A] (x : Nat) (f : Nat → A) : A :=
    match x with
      | 0 => 0
      | n + 1 => sum_less n f + f n
-/

/- Definitions -/
def nat_even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

def nat_odd (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k + 1

def extendPO {A : Type} (R : BinRel A) (b : A) (x y : A) : Prop :=
    R x y ∨ (R x b ∧ ¬R y b)

def fact (x : Nat) : Nat :=
    match x with
      | 0 => 1
      | n + 1 => (n + 1) * fact n

def Fib (x : Nat) : Nat :=
    match x with
      | 0 => 0
      | 1 => 1
      | n + 2 => Fib n + Fib (n + 1)

def rep_image {A : Type} (f : A → A) (x : Nat) (B : Set A) : Set A :=
    match x with
      | 0 => B
      | n + 1 => image f (rep_image f n B)

def cumul_image {A : Type} (f : A → A) (B : Set A) : Set A :=
    { x : A | ∃ (n : Nat), x ∈ rep_image f n B }

def rep_image_family {A : Type}
    (F : Set (A → A)) (x : Nat) (B : Set A) : Set A :=
    match x with
      | 0 => B
      | n + 1 => { x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F n B) }

def cumul_image_family {A : Type}
    (F : Set (A → A)) (B : Set A) : Set A :=
    { x : A | ∃ (n : Nat), x ∈ rep_image_family F n B }

def image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
    { z : A | ∃ (x y : A), x ∈ B ∧ y ∈ B ∧ z = f x y }

def rep_image2 {A : Type}
    (f : A → A → A) (x : Nat) (B : Set A) : Set A :=
    match x with
      | 0 => B
      | n + 1 => image2 f (rep_image2 f n B)

def cumul_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
    { x : A | ∃ (n : Nat), x ∈ rep_image2 f n B }

def un_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
    B ∪ (image2 f B)

def rep_un_image2 {A : Type}
    (f : A → A → A) (x : Nat) (B : Set A) : Set A :=
    match x with
      | 0 => B
      | n + 1 => un_image2 f (rep_un_image2 f n B)

def cumul_un_image2 {A : Type}
    (f : A → A → A) (B : Set A) : Set A :=
    { x : A | ∃ (n : Nat), x ∈ rep_un_image2 f n B }

def idExt (A : Type) : Set (A × A) := { (x, y) : A × A | x = y }

def rep_comp {A : Type} (R : Set (A × A)) (x : Nat) : Set (A × A) :=
    match x with
      | 0 => idExt A
      | n + 1 => comp (rep_comp R n) R

def cumul_rep_comp {A : Type} (R : Set (A × A)) : Set (A × A) :=
    { (x, y) : A × A | ∃ n ≥ 1, (x, y) ∈ rep_comp R n }

def transExt {A : Type} (R : Set (A × A)) : Prop :=
    ∀ (x y z : A), (x, y) ∈ R → (y, z) ∈ R → (x, z) ∈ R

/- Section 6.1 -/
theorem Like_Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 + 2 * n := by
  by_induc
  · -- Base Case
    define         --Goal: ∃ (c : Nat), 0 ^ 3 + 2 * 0 = 3 * c
    apply Exists.intro 0
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : 3 ∣ n ^ 3 + 2 * n
    define at ih   --ih: ∃ (c : Nat), n ^ 3 + 2 * n = 3 * c
    obtain (k : Nat) (h1 : n ^ 3 + 2 * n = 3 * k) from ih
    define         --Goal: ∃ (c : Nat), (n + 1) ^ 3 + 2 * (n + 1) = 3 * c
    apply Exists.intro (k + n ^ 2 + n + 1)
    show (n + 1) ^ 3 + 2 * (n + 1) = 3 * (k + n ^ 2 + n + 1) from
      calc (n + 1) ^ 3 + 2 * (n + 1)
          = n ^ 3 + 2 * n + 3 * n ^ 2 + 3 * n + 3 := by ring
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
          = (Sum i from 0 to n, 2 ^ i) + 2 ^ (n + 1) + 1 :=
            by rw [sum_from_zero_step]
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
          = 2 * 2 ^ n := by ring
        _ > n ^ 2 + 2 * n + 1 := by linarith
        _ = (n + 1) ^ 2 := by ring
    done
  done

#eval 2 - 3     --Answer: 0

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
    rewrite [sum_from_zero_step, ih]
      --Goal: 2 ^ (n + 1) - 1 + 2 ^ (n + 1) = 2 ^ (n + 1 + 1) - 1
    ring
    done
  done

-- Exercises
-- 1.
theorem Like_Exercise_6_1_1 :
    ∀ (n : Nat), 2 * Sum i from 0 to n, i = n * (n + 1) := sorry

-- 2.
theorem Like_Exercise_6_1_4 :
    ∀ (n : Nat), Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2 := sorry

-- 3.
theorem Exercise_6_1_9a : ∀ (n : Nat), 2 ∣ n ^ 2 + n := sorry

-- 4.
theorem Exercise_6_1_13 :
    ∀ (a b : Int) (n : Nat), (a - b) ∣ (a ^ n - b ^ n) := sorry

-- 5.
theorem Exercise_6_1_15 : ∀ n ≥ 10, 2 ^ n > n ^ 3 := sorry

-- 6.
theorem Exercise_6_1_16a1 :
    ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

-- 7.
theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := sorry

/- Section 6.2 -/
lemma Lemma_6_2_1_1 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : R b c) : minimalElt R b B := by
  define at h3
    --h3: c ∈ B \ {b} ∧ ¬∃ (x : A), x ∈ B \ {b} ∧ R x c ∧ x ≠ c
  define  --Goal: b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  apply And.intro h2  --Goal: ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  contradict h3.right with h5
  obtain (x : A) (h6 : x ∈ B ∧ R x b ∧ x ≠ b) from h5
  apply Exists.intro x
  apply And.intro
  · -- Proof that x ∈ B \ {b}
    show x ∈ B \ {b} from And.intro h6.left h6.right.right
    done
  · -- Proof that R x c ∧ x ≠ c
    have Rtrans : transitive R := h1.right.left
    have h7 : R x c := Rtrans x b c h6.right.left h4
    apply And.intro h7
    by_contra h8
    rewrite [h8] at h6
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
    define         --Goal: b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
    apply And.intro
    · -- Proof that b ∈ B
      rewrite [h3]    --Goal: b ∈ {b}
      define
      rfl
      done
    · -- Proof that nothing in B is smaller than b
      by_contra h4
      obtain (x : A) (h5 : x ∈ B ∧ R x b ∧ x ≠ b) from h4
      have h6 : x ∈ B := h5.left
      rewrite [h3] at h6   --h6: x ∈ {b}
      define at h6         --h6: x = b
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
    let B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h3 h5
    obtain (c : A) (h7 : minimalElt R c B') from ih B' h6
    by_cases h8 : R b c
    · -- Case 1. h8: R b c
      have h9 : minimalElt R b B := Lemma_6_2_1_1 h h5 h7 h8
      show ∃ (x : A), minimalElt R x B from Exists.intro b h9
      done
    · -- Case 2. h8: ¬R b c
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
  define at h1     --h1: ¬(R x b ∨ R x b ∧ ¬R b b)
  demorgan at h1   --h1: ¬R x b ∧ ¬(R x b ∧ ¬R b b)
  define           --Goal: R b x ∨ R b b ∧ ¬R x b
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
    define at h2     --h2 : ¬∃ (x : A), x ∈ B
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
    fix B
    assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    obtain (b : A) (h5 : b ∈ B) from nonempty_of_pos_numElts h2 h3
    let B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h2 h5
    have h7 : ∃ (T : BinRel A), partial_order T ∧
      (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T x y ∨ T y x := ih B' h6
    obtain (T' : BinRel A)
      (h8 : partial_order T' ∧ (∀ (x y : A), R x y → T' x y) ∧
      ∀ (x : A), x ∈ B' → ∀ (y : A), T' x y ∨ T' y x) from h7
    have h9 : partial_order T' := h8.left
    let T : BinRel A := extendPO T' b
    apply Exists.intro T
    apply And.intro (extendPO_is_po T' b h9)
    apply And.intro
    · -- Proof that T extends R
      fix x : A; fix y : A
      assume h10 : R x y
      have h11 : T' x y := h8.right.left x y h10
      show T x y from (extendPO_extends T' b x y h11)
      done
    · -- Proof that everything in B comparable to everything under T
      fix x : A
      assume h10 : x ∈ B
      by_cases h11 : x = b
      · -- Case 1. h11: x = b
        rewrite [h11]
        show ∀ (y : A), T b y ∨ T y b from extendPO_all_comp T' b h9
        done
      · -- Case 2. h11: x ≠ b
        have h12 : x ∈ B' := And.intro h10 h11
        fix y : A
        have h13 : T' x y ∨ T' y x := h8.right.right x h12 y
        by_cases on h13
        · -- Case 1. h13: T' x y
          show T x y ∨ T y x from
            Or.inl (extendPO_extends T' b x y h13)
          done
        · -- Case 2. h13: T' y x
          show T x y ∨ T y x from
            Or.inr (extendPO_extends T' b y x h13)
          done
        done
      done
    done
  done

-- Exercises
-- 1.
lemma Lemma_6_2_1_2_ex {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := sorry

-- 2.
lemma extendPO_is_ref_ex {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := sorry

-- 3.
lemma extendPO_is_trans_ex {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := sorry

-- 4.
lemma extendPO_is_antisymm_ex {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := sorry

-- 5.
theorem Exercise_6_2_3 (A : Type) (R : BinRel A)
    (h : total_order R) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ (b : A), smallestElt R b B := sorry

-- 6.
--Hint:  First prove that R is reflexive
theorem Exercise_6_2_4a {A : Type} (R : BinRel A)
    (h : ∀ (x y : A), R x y ∨ R y x) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ x ∈ B, ∀ y ∈ B, ∃ (z : A), R x z ∧ R z y := sorry

-- 7.
theorem Like_Exercise_6_2_16 (f : Nat → Nat) (h : one_to_one f) :
    ∀ (n : Nat) (A : Set Nat), numElts A n →
    closed f A → ∀ y ∈ A, ∃ x ∈ A, f x = y := sorry

-- 8.
--Hint:  Use Exercise_6_2_2
theorem Example_6_2_2 {A : Type} (R : BinRel A)
    (h1 : ∃ (n : Nat), numElts { x : A | x = x } n)
    (h2 : partial_order R) : ∃ (T : BinRel A),
      total_order T ∧ ∀ (x y : A), R x y → T x y := sorry

/- Section 6.3 -/
#eval fact 4   --Answer: 24

theorem Example_6_3_1 : ∀ n ≥ 4, fact n > 2 ^ n := by
  by_induc
  · -- Base Case
    norm_num
    done
  · -- Induction Step
    fix n : Nat
    assume h1 : n ≥ 4
    assume ih : fact n > 2 ^ n
    have h2 : n + 1 > 0 := by linarith
    have h3 : n + 1 > 2 := by linarith
    have h4 : 2 > 0 := by linarith
    have h5 : 2 ^ n > 0 := pow_pos h4 n
    show fact (n + 1) > 2 ^ (n + 1) from
      calc fact (n + 1)
          = (n + 1) * fact n := by rfl
        _ > (n + 1) * 2 ^ n := Nat.mul_lt_mul_of_pos_left ih h2
        _ > 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_right h3 h5
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
    --Goal: ∀ (n : Nat), a ^ (m + n) = a ^ m * a ^ n
  by_induc
  · -- Base Case
    show a ^ (m + 0) = a ^ m * a ^ 0 from
      calc a ^ (m + 0)
          = a ^ m := by rfl
        _ = a ^ m * 1 := (mul_one (a ^ m)).symm
        _ = a ^ m * a ^ 0 := by rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : a ^ (m + n) = a ^ m * a ^ n
    show a ^ (m + (n + 1)) = a ^ m * a ^ (n + 1) from
      calc a ^ (m + (n + 1))
          = a ^ ((m + n) + 1) := by rw [add_assoc]
        _ = a * a ^ (m + n) := by rfl
        _ = a * (a ^ m * a ^ n) := by rw [ih]
        _ = a ^ m * (a * a ^ n) :=
            by rw [←mul_assoc, mul_comm a, mul_assoc]
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
    have h2 : 1 + x ≥ 0 := by linarith
    have h3 : n * x * x ≥ 0 := by
      have h4 : x * x ≥ 0 := mul_self_nonneg x
      have h5 : (↑n : Real) ≥ 0 := Nat.cast_nonneg n
      show n * x * x ≥ 0 from 
        calc n * x * x
            = n * (x * x) := mul_assoc _ _ _
          _ ≥ n * 0 := mul_le_mul_of_nonneg_left h4 h5
          _ = 0 := by ring
      done
    show (1 + x) ^ (n + 1) ≥ 1 + (↑n + 1) * x from
      calc (1 + x) ^ (n + 1)
          = (1 + x) * (1 + x) ^ n := by rfl
        _ ≥ (1 + x) * (1 + n * x) := mul_le_mul_of_nonneg_left ih h2
        _ = 1 + x + n * x + n * x * x := by ring
        _ ≥ 1 + x + n * x + 0 := add_le_add_left h3 _
        _ = 1 + (↑n + 1) * x := by ring
    done
  done

-- Exercises
-- 1.
theorem Exercise_6_3_4 : ∀ (n : Nat),
    3 * (Sum i from 0 to n, (2 * i + 1) ^ 2) =
    (n + 1) * (2 * n + 1) * (2 * n + 3) := sorry

-- 2.
theorem Exercise_6_3_7b (f : Nat → Real) (c : Real) : ∀ (n : Nat),
    Sum i from 0 to n, c * f i = c * Sum i from 0 to n, f i := sorry

-- 3.
theorem fact_pos : ∀ (n : Nat), fact n ≥ 1 := sorry

-- 4.
--Hint:  Use the theorem fact_pos from the previous exercise
theorem Exercise_6_3_13a (k : Nat) : ∀ (n : Nat),
    fact (k ^ 2 + n) ≥ k ^ (2 * n) := sorry

-- 5.
--Hint:  Use the theorem in the previous exercise.
--You may find it useful to first prove a lemma:
--∀ (k : Nat), 2 * k ^ 2 + 1 ≥ k
theorem Exercise_6_3_13b (k : Nat) : ∀ n ≥ 2 * k ^ 2,
    fact n ≥ k ^ n := sorry

-- 6.
def seq_6_3_15 (x : Nat) : Int :=
    match x with
      | 0 => 0
      | n + 1 => 2 * seq_6_3_15 n + n

theorem Exercise_6_3_15 : ∀ (n : Nat),
    seq_6_3_15 n = 2 ^ n - n - 1 := sorry

-- 7.
def seq_6_3_16 (x : Nat) : Nat :=
    match x with
      | 0 => 2
      | n + 1 => (seq_6_3_16 n) ^ 2

theorem Exercise_6_3_16 : ∀ (n : Nat),
    seq_6_3_16 n = ___ := sorry

/- Section 6.4 -/
theorem Example_6_4_1 : ∀ m > 0, ∀ (n : Nat),
    ∃ (q r : Nat), n = q * m + r ∧ r < m := by
  fix m : Nat
  assume h1 : m > 0
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, ∃ (q r : Nat), n_1 = q * m + r ∧ r < m
  by_cases h2 : n < m
  · -- Case 1. h2: n < m
    apply Exists.intro 0
    apply Exists.intro n     --Goal: n = 0 * m + n ∧ n < m
    apply And.intro _ h2
    ring
    done
  · -- Case 2. h2: ¬n < m
    have h3 : m ≤ n := by linarith
    let k : Nat := n - m
    have h4 : k < n := Nat.sub_lt_of_pos_le m n h1 h3
    have h5 : ∃ (q r : Nat), k = q * m + r ∧ r < m := ih k h4
    obtain (q' : Nat)
      (h6 : ∃ (r : Nat), k = q' * m + r ∧ r < m) from h5
    obtain (r' : Nat) (h7 : k = q' * m + r' ∧ r' < m) from h6
    apply Exists.intro (q' + 1)
    apply Exists.intro r'     --Goal: n = (q' + 1) * m + r' ∧ r' < m
    apply And.intro _ h7.right
    show n = (q' + 1) * m + r' from
      calc n
          = k + m := (Nat.sub_add_cancel h3).symm
        _ = q' * m + r' + m := by rw [h7.left]
        _ = (q' + 1) * m + r' := by ring
    done
  done

example : ∀ (n : Nat), Fib n < 2 ^ n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, Fib n_1 < 2 ^ n_1
  by_cases h1 : n = 0
  · -- Case 1. h1: n = 0
    rewrite [h1]          --Goal: Fib 0 < 2 ^ 0
    norm_num
    done
  · -- Case 2. h1: n ≠ 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2: n = 1
      rewrite [h2]        --Goal: Fib 1 < 2 ^ 1
      norm_num
      done
    · -- Case 2.2. h2: n ≠ 1
      have h3 : 2 ≤ n := by
        have h4 : 1 ≤ n := Nat.pos_of_ne_zero h1
        show 2 ≤ n from lt_of_le_of_ne' h4 h2
        done
      let k : Nat := n - 2
      have h4 : k + 2 = n := Nat.sub_add_cancel h3
      have h5 : k < n := by linarith
      have h6 : Fib k < 2 ^ k := ih k h5
      have h7 : k + 1 < n := by linarith
      have h8 : Fib (k + 1) < 2 ^ (k + 1) := ih (k + 1) h7
      have h9 : 3 ≤ 4 := by linarith
      show Fib n < 2 ^ n from
        calc Fib n
            = Fib (k + 2) := by rw [h4]
          _ = Fib k + Fib (k + 1) := by rfl
          _ < 2 ^ k + Fib (k + 1) := add_lt_add_right h6 _
          _ < 2 ^ k + 2 ^ (k + 1) := add_lt_add_left h8 _
          _ = 2 ^ k * 3 := by ring
          _ ≤ 2 ^ k * 4 := Nat.mul_le_mul_left _ h9
          _ = 2 ^ (k + 2) := by ring
          _ = 2 ^ n := by rw [h4]
      done
    done
  done

theorem well_ord_princ (S : Set Nat) (h1 : ∃ (n : Nat), n ∈ S) :
    ∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m := by
  contradict h1 with h2
    --h2: ¬∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m
  quant_neg                   --Goal: ∀ (n : Nat), ¬n ∈ S
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, n_1 ∉ S  --Goal: ¬n ∈ S
  contradict h2 with h3       --h3: n ∈ S
    --Goal: ∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m
  apply Exists.intro n
  apply And.intro h3          --Goal: ∀ (m : Nat), m ∈ S → m ≤ y
  fix m : Nat
  assume h4 : m ∈ S
  have h5 : m < n → ¬m ∈ S := ih m
  contrapos at h5             --h5: m ∈ S → ¬m < n
  have h6 : ¬m < n := h5 h4
  linarith
  done

lemma sq_even_iff_even (n : Nat) : nat_even (n * n) ↔ nat_even n := sorry

theorem sqrt_2_irrat :
    ¬∃ (q p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 := by
  let S : Set Nat :=
    { q : Nat | ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 }
  by_contra h1
  have h2 : ∃ (q : Nat), q ∈ S := h1
  have h3 : ∃ (q : Nat), q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r :=
    well_ord_princ S h2
  obtain (q : Nat) (h4 : q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r) from h3
  have h4l : q ∈ S := h4.left
  define at h4l     --h4l: ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0
  obtain (p : Nat) (h5 : p * p = 2 * (q * q) ∧ q ≠ 0) from h4l
  have h5l : p * p = 2 * (q * q) := h5.left
  have h6 : nat_even (p * p) := Exists.intro (q * q) h5l
  rewrite [sq_even_iff_even p] at h6    --h6: nat_even p
  obtain (p' : Nat) (h7 : p = 2 * p') from h6
  have h8 : 2 * (2 * (p' * p')) = 2 * (q * q) := by
    rewrite [←h5l, h7]
    ring
    done
  have h9 : 2 > 0 := by norm_num
  rewrite [mul_left_cancel_iff_of_pos h9] at h8
    --h8: 2 * (p' * p') = q * q
  have h10 : nat_even (q * q) := Exists.intro (p' * p') h8.symm
  rewrite [sq_even_iff_even q] at h10   --h10: nat_even q
  obtain (q' : Nat) (h11 : q = 2 * q') from h10
  have h12 : 2 * (p' * p') = 2 * (2 * (q' * q')) := by
    rewrite [h8, h11]
    ring
    done
  rewrite [mul_left_cancel_iff_of_pos h9] at h12
    --h12: p' * p' = 2 * (q' * q')
  have h13 : q' ≠ 0 := by
    contradict h5.right with h14
    rewrite [h11, h14]
    rfl
    done
  have h14 : q' ∈ S := Exists.intro p' (And.intro h12 h13)
  have h15 : q ≤ q' := h4.right q' h14
  rewrite [h11] at h15        --h15: 2 * q' ≤ q'
  contradict h13
  linarith
  done

-- Exercises
-- 1.
--Hint: Use Exercise_6_1_16a1 and Exercise_6_1_16a2
lemma sq_even_iff_even_ex (n : Nat) :
    nat_even (n * n) ↔ nat_even n := sorry

-- 2.
--This theorem proves that the square root of 6 is irrational
theorem Exercise_6_4_4a :
    ¬∃ (q p : Nat), p * p = 6 * (q * q) ∧ q ≠ 0 := sorry

-- 3.
theorem Exercise_6_4_5 :
    ∀ n ≥ 12, ∃ (a b : Nat), 3 * a + 7 * b = n := sorry

-- 4.
theorem Exercise_6_4_7a : ∀ (n : Nat),
    (Sum i from 0 to n, Fib i) + 1 = Fib (n + 2) := sorry

-- 5.
theorem Exercise_6_4_7c : ∀ (n : Nat),
    Sum i from 0 to n, Fib (2 * i + 1) = Fib (2 * n + 2) := sorry

-- 6.
theorem Exercise_6_4_8a : ∀ (m n : Nat) ,
    Fib (m + n + 1) = Fib m * Fib n + Fib (m + 1) * Fib (n + 1) := sorry

-- 7.
theorem Exercise_6_4_8d : ∀ (m k : Nat), Fib m ∣ Fib (m * k) := sorry

-- 8.
def Fib_like (x : Nat) : Nat :=
    match x with
      | 0 => 1
      | 1 => 2
      | n + 2 => 2 * (Fib_like n) + Fib_like (n + 1)

theorem Fib_like_formula : ∀ (n : Nat), Fib_like n = 2 ^ n := sorry

-- 9.
def triple_rec (x : Nat) : Nat :=
    match x with
      | 0 => 0
      | 1 => 2
      | 2 => 4
      | n + 3 => 4 * triple_rec n +
                  6 * triple_rec (n + 1) + triple_rec (n + 2)

theorem triple_rec_formula :
    ∀ (n : Nat), triple_rec n = 2 ^ n * Fib n := sorry

-- 10.
lemma quot_rem_unique_lemma {m q r q' r' : Nat}
    (h1 : q * m + r = q' * m + r') (h2 : r' < m) : q ≤ q' := sorry

theorem quot_rem_unique (m q r q' r' : Nat)
    (h1 : q * m + r = q' * m + r') (h2 : r < m) (h3 : r' < m) :
    q = q' ∧ r = r' := sorry

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
    rewrite [rep_image_base]          --Goal: B ⊆ D
    show B ⊆ D from h1
    done
  · -- Induction Step
    fix n : Nat
    assume ih : rep_image f n B ⊆ D   --Goal: rep_image f (n + 1) B ⊆ D
    fix x : A
    assume h3 : x ∈ rep_image f (n + 1) B  --Goal: x ∈ D
    rewrite [rep_image_step] at h3
    define at h3    --h3: ∃ (x_1 : A), x_1 ∈ rep_image f n B ∧ f x_1 = x
    obtain (b : A) (h4 : b ∈ rep_image f n B ∧ f b = x) from h3
    rewrite [←h4.right] --Goal: f b ∈ D    
    have h5 : b ∈ D := ih h4.left
    define at h2        --h2: ∀ (x : A), x ∈ D → f x ∈ D
    show f b ∈ D from h2 b h5
    done
  done

theorem Theorem_6_5_1 {A : Type} (f : A → A) (B : Set A) :
    closure f B (cumul_image f B) := by
  define
  apply And.intro
  · -- Proof that cumul_image f B ∈ { D : Set A | B ⊆ D ∧ closed f D }
    define  --Goal: B ⊆ cumul_image f B ∧ closed f (cumul_image f B)
    apply And.intro
    · -- Proof that B ⊆ cumul_image f B
      fix x : A
      assume h1 : x ∈ B
      define     --Goal: ∃ (n : Nat), x ∈ rep_image f n B
      apply Exists.intro 0
      rewrite [rep_image_base]  --Goal: x ∈ B
      show x ∈ B from h1
      done
    · -- Proof that cumul_image f B closed under f
      define
      fix x : A
      assume h1 : x ∈ cumul_image f B  --Goal: f x ∈ cumul_image f B
      define at h1
      obtain (m : Nat) (h2 : x ∈ rep_image f m B) from h1
      define     --Goal: ∃ (n : Nat), f x ∈ rep_image f n B
      apply Exists.intro (m + 1) --Goal:  f x ∈ rep_image f (m + 1) B
      rewrite [rep_image_step]   --Goal: f x ∈ image f (rep_image f m B)
      define     --Goal: ∃ (x_1 : A), x_1 ∈ rep_image f m B ∧ f x_1 = f x
      apply Exists.intro x  --Goal: x ∈ rep_image f m B ∧ f x = f x
      apply And.intro h2
      rfl
      done
    done
  · -- Proof that cumul_image f B is smallest
    fix D : Set A
    assume h1 : D ∈ { D : Set A | B ⊆ D ∧ closed f D }
    define at h1  --h1: B ⊆ D ∧ closed f D
    define   --Goal: ∀ ⦃a : A⦄, a ∈ cumul_image f B → a ∈ D
    fix x : A
    assume h2 : x ∈ cumul_image f B  --Goal: x ∈ D
    define at h2  --h2: ∃ (n : Nat), x ∈ rep_image f n B
    obtain (m : Nat) (h3 : x ∈ rep_image f m B) from h2
    have h4 : rep_image f m B ⊆ D :=
      rep_image_sub_closed h1.left h1.right m
    show x ∈ D from h4 h3
    done
  done

-- Exercises
-- 1.
theorem rep_image_family_base {A : Type}
    (F : Set (A → A)) (B : Set A) : rep_image_family F 0 B = B := by rfl

theorem rep_image_family_step {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) :
    rep_image_family F (n + 1) B =
    { x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F n B) } := by rfl

lemma rep_image_family_sub_closed {A : Type}
    (F : Set (A → A)) (B D : Set A)
    (h1 : B ⊆ D) (h2 : closed_family F D) :
    ∀ (n : Nat), rep_image_family F n B ⊆ D := sorry

theorem Exercise_6_5_3 {A : Type} (F : Set (A → A)) (B : Set A) :
    closure_family F B (cumul_image_family F B) := sorry

-- 2.
theorem rep_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_image2 f 0 B = B := by rfl

theorem rep_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_image2 f (n + 1) B = image2 f (rep_image2 f n B) := by rfl

--You won't be able to complete this proof
theorem Exercise_6_5_6 {A : Type} (f : A → A → A) (B : Set A) :
    closed2 f (cumul_image2 f B) := sorry

-- 3.
theorem rep_un_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_un_image2 f 0 B = B := by rfl

theorem rep_un_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_un_image2 f (n + 1) B =
    un_image2 f (rep_un_image2 f n B) := by rfl

theorem Exercise_6_5_8a {A : Type} (f : A → A → A) (B : Set A) :
    ∀ (m n : Nat), m ≤ n →
    rep_un_image2 f m B ⊆ rep_un_image2 f n B := sorry

lemma rep_un_image2_sub_closed {A : Type} {f : A → A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed2 f D) :
    ∀ (n : Nat), rep_un_image2 f n B ⊆ D := sorry

lemma closed_lemma
    {A : Type} {f : A → A → A} {B : Set A} {x y : A} {nx ny n : Nat}
    (h1 : x ∈ rep_un_image2 f nx B) (h2 : y ∈ rep_un_image2 f ny B)
    (h3 : nx ≤ n) (h4 : ny ≤ n) :
    f x y ∈ cumul_un_image2 f B := sorry

theorem Exercise_6_5_8b {A : Type} (f : A → A → A) (B : Set A) :
    closure2 f B (cumul_un_image2 f B) := sorry

-- 4.
theorem rep_comp_one {A : Type} (R : Set (A × A)) :
    rep_comp R 1 = R := sorry

-- 5.
theorem Exercise_6_5_11 {A : Type} (R : Set (A × A)) :
    ∀ (m n : Nat), rep_comp R (m + n) =
    comp (rep_comp R m) (rep_comp R n) := sorry

-- 6.
lemma rep_comp_sub_trans {A : Type} {R S : Set (A × A)}
    (h1 : R ⊆ S) (h2 : transExt S): ∀ n ≥ 1, rep_comp R n ⊆ S := sorry

-- 7.
theorem Exercise_6_5_14 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (cumul_rep_comp R)
    { S : Set (A × A) | R ⊆ S ∧ transExt S } := sorry