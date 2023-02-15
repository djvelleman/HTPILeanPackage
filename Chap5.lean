import HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true

/- Definitions from Chapter 4 -/
def Dom {A B : Type} (R : Set (A × B)) : Set A :=
    { a : A | ∃ (b : B), (a, b) ∈ R }

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
    { b : B | ∃ (a : A), (a, b) ∈ R }

def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
    { (b, a) : B × A | (a, b) ∈ R }

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

def empty {A : Type} (X : Set A) : Prop := ¬∃ (x : A), x ∈ X 

def pairwise_disjoint {A : Type} (F : Set (Set A)) : Prop :=
    ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → empty (X ∩ Y)

def partition {A : Type} (F : Set (Set A)) : Prop :=
    (∀ (x : A), x ∈ ⋃₀ F) ∧ pairwise_disjoint F ∧ ∀ X ∈ F, ¬empty X

def EqRelFromPart {A : Type} (F : Set (Set A)) (x y : A) : Prop :=
    ∃ X ∈ F, x ∈ X ∧ y ∈ X

/- Definitions and theorems in HTPIDefs
def graph {A B : Type} (f : A → B) : Set (A × B) :=
    { (a, b) : A × B | f a = b }

def is_func_graph {A B : Type} (G : Set (A × B)) : Prop :=
    ∀ (x : A), ∃! (y : B), (x, y) ∈ G

theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F := by
-/

/- Definitions -/
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

/- Section 5.1 -/
theorem simp_graph {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ graph f ↔ f a = b := by rfl

theorem Theorem_5_1_4 {A B : Type} (f g : A → B) :
    (∀ (a : A), f a = g a) → f = g := funext

example {A B : Type} (f g : A → B) :
    graph f = graph g → f = g := by
  assume h1 : graph f = graph g  --Goal: f = g
  apply funext                   --Goal: ∀ (x : A), f x = g x
  fix x : A
  have h2 : (x, f x) ∈ graph f := by
    define                       --Goal: f x = f x
    rfl
    done
  rewrite [h1] at h2             --h2: (x, f x) ∈ graph g
  define at h2                   --h2: g x = f x
  show f x = g x from h2.symm
  done

def square1 (n : Nat) : Nat := n ^ 2

def square2 : Nat → Nat := fun (n : Nat) => n ^ 2

example : square1 = square2 := by rfl

#eval square1 7     --Answer: 49

theorem Theorem_5_1_5 {A B C : Type} (f : A → B) (g : B → C) :
    ∃ (h : A → C), graph h = comp (graph g) (graph f) := by
  let h : A → C := fun (x : A) => g (f x)
  apply Exists.intro h
  apply Set.ext
  fix (a, c) : A × C
  apply Iff.intro
  · -- Proof that (a, c) ∈ graph h → (a, c) ∈ comp (graph g) (graph f)
    assume h1 : (a, c) ∈ graph h
    define at h1  --h1: h a = c
    define        --Goal: ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    apply Exists.intro (f a)
    apply And.intro
    · -- Proof that (a, f a) ∈ graph f
      define
      rfl
      done
    · -- Proof that (f a, c) ∈ graph g
      define
      show g (f a) = c from h1
      done
    done
  · -- Proof that (a, c) ∈ comp (graph g) (graph f) → (a, c) ∈ graph h
    assume h1 : (a, c) ∈ comp (graph g) (graph f)
    define        --Goal: h a = c
    define at h1  --h1: ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    obtain (b : B) (h2 : (a, b) ∈ graph f ∧ (b, c) ∈ graph g) from h1
    have h3 : (a, b) ∈ graph f := h2.left
    have h4 : (b, c) ∈ graph g := h2.right
    define at h3          --h3: f a = b
    define at h4          --h4: g b = c
    rewrite [←h3] at h4   --h4: g (f a) = c
    show h a = c from h4
    done
  done

example {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by rfl

example {A B : Type} (f : A → B) : f ∘ id = f := by rfl

example {A B : Type} (f : A → B) : id ∘ f = f := by rfl

-- Exercises
-- 1.
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := sorry

-- 2.
theorem Exercise_5_1_13a
    {A B C : Type} (R : Set (A × B)) (S : Set (B × C)) (f : A → C)
    (h1 : ∀ (b : B), b ∈ Ran R ∧ b ∈ Dom S) (h2 : graph f = comp S R) :
    is_func_graph S := sorry

-- 3.
theorem Exercise_5_1_14a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : A), R x y ↔ S (f x) (f y)) :
    reflexive S → reflexive R := sorry

-- 4.
--You might not be able to complete this proof
theorem Exercise_5_1_15a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    reflexive R → reflexive S := sorry

-- 5.
--You might not be able to complete this proof
theorem Exercise_5_1_15c
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v) :
    transitive R → transitive S := sorry

-- 6.
theorem Exercise_5_1_16b
    {A B : Type} (R : BinRel B) (S : BinRel (A → B))
    (h : ∀ (f g : A → B), S f g ↔ ∀ (x : A), R (f x) (g x)) :
    symmetric R → symmetric S := sorry

-- 7.
theorem Exercise_5_1_17a {A : Type} (f : A → A) (a : A)
    (h : ∀ (x : A), f x = a) : ∀ (g : A → A), f ∘ g = f := sorry

-- 8.
theorem Exercise_5_1_17b {A : Type} (f : A → A) (a : A)
    (h : ∀ (g : A → A), f ∘ g = f) :
    ∃ (y : A), ∀ (x : A), f x = y := sorry

/- Section 5.2 -/
theorem Theorem_5_2_5_1 {A B C : Type} (f : A → B) (g : B → C) :
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  assume h1 : one_to_one f
  assume h2 : one_to_one g
  define at h1  --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  define at h2  --h2: ∀ (x1 x2 : B), g x1 = g x2 → x1 = x2
  define        --Goal: ∀ (x1 x2 : A), (g ∘ f) x1 = (g ∘ f) x2 → x1 = x2
  fix a1 : A
  fix a2 : A    --Goal: (g ∘ f) a1 = (g ∘ f) a2 → a1 = a2
  define : (g ∘ f) a1; define : (g ∘ f) a2
                --Goal: g (f a1) = g (f a2) → a1 = a2
  assume h3 : g (f a1) = g (f a2)
  have h4 : f a1 = f a2 := h2 (f a1) (f a2) h3
  show a1 = a2 from h1 a1 a2 h4
  done

theorem Theorem_5_2_5_2 {A B C : Type} (f : A → B) (g : B → C) :
    onto f → onto g → onto (g ∘ f) := by
  assume h1 : onto f
  assume h2 : onto g
  define at h1           --h1: ∀ (y : B), ∃ (x : A), f x = y
  define at h2           --h2: ∀ (y : C), ∃ (x : B), g x = y
  define                 --Goal: ∀ (y : C), ∃ (x : A), (g ∘ f) x = y
  fix c : C
  obtain (b : B) (h3 : g b = c) from h2 c
  obtain (a : A) (h4 : f a = b) from h1 b
  apply Exists.intro a   --Goal: (g ∘ f) a = c
  define : (g ∘ f) a     --Goal: g (f a) = c
  rewrite [←h4] at h3
  show g (f a) = c from h3
  done

-- Exercises
-- 1.
theorem Exercise_5_2_10a {A B C : Type} (f: A → B) (g : B → C) :
    onto (g ∘ f) → onto g := sorry

-- 2.
theorem Exercise_5_2_10b {A B C : Type} (f: A → B) (g : B → C) :
    one_to_one (g ∘ f) → one_to_one f := sorry

-- 3.
theorem Exercise_5_2_11a {A B C : Type} (f: A → B) (g : B → C) :
    onto f → ¬(one_to_one g) → ¬(one_to_one (g ∘ f)) := sorry

-- 4.
theorem Exercise_5_2_11b {A B C : Type} (f: A → B) (g : B → C) :
    ¬(onto f) → one_to_one g → ¬(onto (g ∘ f)) := sorry

-- 5.
theorem Exercise_5_2_12 {A B : Type} (f : A → B) (g : B → Set A)
    (h : ∀ (b : B), g b = { a : A | f a = b }) :
    onto f → one_to_one g := sorry

-- 6.
theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := sorry

-- 7.
theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := sorry

-- 8.
theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := sorry

-- 9.
theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := sorry

-- 10.
theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := sorry

/- Section 5.3 -/
theorem Theorem_5_3_1 {A B : Type}
    (f : A → B) (h1 : one_to_one f) (h2 : onto f) :
    ∃ (g : B → A), graph g = inv (graph f) := by
  rewrite [func_from_graph]   --Goal: is_func_graph (inv (graph f))
  define        --Goal: ∀ (x : B), ∃! (y : A), (x, y) ∈ inv (graph f)
  fix b : B
  exists_unique
  · -- Existence
    define at h2          --h2: ∀ (y : B), ∃ (x : A), f x = y
    obtain (a : A) (h4 : f a = b) from h2 b
    apply Exists.intro a  --Goal: (b, a) ∈ inv (graph f)
    define                --Goal: f a = b
    show f a = b from h4
    done
  · -- Uniqueness
    fix a1 : A; fix a2 : A
    assume h3 : (b, a1) ∈ inv (graph f)
    assume h4 : (b, a2) ∈ inv (graph f) --Goal: a1 = a2
    define at h3          --h3: f a1 = b
    define at h4          --h4: f a2 = b
    rewrite [←h4] at h3   --h3: f a1 = f a2
    define at h1          --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    show a1 = a2 from h1 a1 a2 h3
    done
  done

theorem Theorem_5_3_2_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : g ∘ f = id := by
  apply funext           --Goal: ∀ (x : A), (g ∘ f) x = id x
  fix a : A              --Goal: (g ∘ f) a = id a
  have h2 : (f a, a) ∈ graph g := by
    rewrite [h1]         --Goal: (f a, a) ∈ inv (graph f)
    define               --Goal: f a = f a
    rfl
    done
  define at h2           --h2: g (f a) = a
  show (g ∘ f) a = id a from h2
  done

theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

theorem Theorem_5_3_3_1 {A B : Type} (f : A → B) :
    (∃ (g : B → A), g ∘ f = id) → one_to_one f := by
  assume h1 : ∃ (g : B → A), g ∘ f = id
  obtain (g : B → A) (h2 : g ∘ f = id) from h1
  define              --Goal: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  fix a1 : A; fix a2 : A
  assume h3 : f a1 = f a2
  show a1 = a2 from
    calc a1
        = id a1 := by rfl
      _ = (g ∘ f) a1 := by rw [h2]
      _ = g (f a1) := by rfl
      _ = g (f a2) := by rw [h3]
      _ = (g ∘ f) a2 := by rfl
      _ = id a2 := by rw [h2]
      _ = a2 := by rfl
  done

theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) :
    (∃ (g : B → A), f ∘ g = id) → onto f := sorry

theorem Theorem_5_3_5 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) (h2 : f ∘ g = id) : graph g = inv (graph f) := by
  have h3 : one_to_one f := Theorem_5_3_3_1 f (Exists.intro g h1)
  have h4 : onto f := Theorem_5_3_3_2 f (Exists.intro g h2)
  obtain (g' : B → A) (h5 : graph g' = inv (graph f))
    from Theorem_5_3_1 f h3 h4
  have h6 : g' ∘ f = id := Theorem_5_3_2_1 f g' h5
  have h7 : g = g' :=
    calc g
        = id ∘ g := by rfl
      _ = (g' ∘ f) ∘ g := by rw [h6]
      _ = g' ∘ (f ∘ g) := by rfl
      _ = g' ∘ id := by rw [h2]
      _ = g' := by rfl
  rewrite [←h7] at h5
  show graph g = inv (graph f) from h5
  done

-- Exercises
-- 1.
theorem Theorem_5_3_2_2_ex {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry

-- 2.
theorem Theorem_5_3_3_2_ex {A B : Type} (f : A → B) :
    (∃ (g : B → A), f ∘ g = id) → onto f := sorry

-- 3.
theorem Exercise_5_3_11a {A B : Type} (f : A → B) (g : B → A) :
    one_to_one f → f ∘ g = id → graph g = inv (graph f) := sorry

-- 4.
theorem Exercise_5_3_11b {A B : Type} (f : A → B) (g : B → A) :
    onto f → g ∘ f = id → graph g = inv (graph f) := sorry

-- 5.
theorem Exercise_5_3_14a {A B : Type} (f : A → B) (g : B → A)
    (h : f ∘ g = id) : ∀ x ∈ Ran (graph g), g (f x) = x := sorry

-- 6.
theorem Exercise_5_3_18 {A B C : Type} (f : A → C) (g : B → C)
    (h1 : one_to_one g) (h2 : onto g) :
    ∃ (h : A → B), g ∘ h = f := sorry

-- Definition for next two exercises:
def conj (A : Type) (f1 f2 : A → A) : Prop :=
    ∃ (g g' : A → A), (f1 = g' ∘ f2 ∘ g) ∧ (g ∘ g' = id) ∧ (g' ∘ g = id)

-- 7.
theorem Exercise_5_3_17a {A : Type} : symmetric (conj A) := sorry

-- 8.
theorem Exercise_5_3_17b {A : Type} (f1 f2 : A → A)
    (h1 : conj A f1 f2) (h2 : ∃ (a : A), f1 a = a) :
    ∃ (a : A), f2 a = a := sorry

/- Section 5.4 -/
theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  let F : Set (Set A) := { D : Set A | B ⊆ D ∧ closed f D }
  let C : Set A := ⋂₀ F
  apply Exists.intro C    --Goal: closure f B C
  define                  --Goal: C ∈ F ∧ ∀ x ∈ F, C ⊆ x
  apply And.intro
  · -- Proof that C ∈ F
    define                  --Goal: B ⊆ C ∧ closed f C
    apply And.intro
    · -- Proof that B ⊆ C
      fix a : A
      assume h1 : a ∈ B       --Goal: a ∈ C
      define                  --Goal: ∀ t ∈ F, a ∈ t
      fix D : Set A
      assume h2 : D ∈ F
      define at h2            --h2: B ⊆ D ∧ closed f D
      show a ∈ D from h2.left h1
      done
    · -- Proof that C is closed under f
      define                  --Goal: ∀ x ∈ C, f x ∈ C
      fix a : A
      assume h1 : a ∈ C       --Goal: f a ∈ C
      define                  --Goal: ∀ t ∈ F, f a ∈ t
      fix D : Set A
      assume h2 : D ∈ F       --Goal: f a ∈ D
      define at h1            --h1: ∀ t ∈ F, a ∈ t
      have h3 : a ∈ D := h1 D h2
      define at h2            --h2: B ⊆ D ∧ closed f D
      have h4 : closed f D := h2.right
      define at h4            --h4: ∀ x ∈ D, f x ∈ D
      show f a ∈ D from h4 a h3
      done
    done
  · -- Proof that C is smallest
    fix D : Set A
    assume h1 : D ∈ F      --Goal: sub A C D
    define
    fix a : A
    assume h2 : a ∈ C       --Goal: a ∈ D
    define at h2            --h2: ∀ t ∈ F, a ∈ t
    show a ∈ D from h2 D h1
    done
  done

def plus (m n : Int) : Int := m + n

def plus' : Int → Int → Int := fun (m n : Int) => m + n

def plus'' : Int → Int → Int := fun (m : Int) => (fun (n : Int) => m + n)

example : plus = plus'' := by rfl

example : plus' = plus'' := by rfl

#eval plus 3 2     --Answer: 5

theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- Exercises
-- 1.
example {A : Type} (F : Set (Set A)) (B : Set A) :
    smallestElt (sub A) B F → B = ⋂₀ F := sorry

-- 2.
def complement {A : Type} (B : Set A) : Set A := { a : A | a ∉ B }

theorem simp_complement {A : Type} (a : A) (B : Set A) :
    a ∈ complement B ↔ a ∉ B := by rfl

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := sorry

-- 3.
theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := sorry

-- 4.
theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := sorry

-- 5.
theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := sorry

-- 6.
theorem Theorem_5_4_9_ex {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

-- 7.
theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := sorry

/- Section 5.5 -/
theorem simp_image {A B : Type} (f : A → B) (X : Set A) (b : B) :
    b ∈ image f X ↔ ∃ x ∈ X, f x = b := by rfl

theorem simp_inverse_image {A B : Type} (f : A → B) (Y : Set B) (a : A) :
    a ∈ inverse_image f Y ↔ f a ∈ Y := by rfl

theorem Theorem_5_5_2_1 {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∩ X) ⊆ image f W ∩ image f X := by
  fix y : B
  assume h1 : y ∈ image f (W ∩ X)  --Goal: y ∈ image f W ∩ image f X
  define at h1                     --h1: ∃ (x : A), x ∈ W ∩ X ∧ f x = y
  obtain (x : A) (h2 : x ∈ W ∩ X ∧ f x = y) from h1
  define : x ∈ W ∩ X at h2         --h2: (x ∈ W ∧ x ∈ X) ∧ f x = y
  apply And.intro
  · -- Proof that y ∈ image f W
    define                           --Goal: ∃ (x : A), x ∈ W ∧ f x = y
    show ∃ (x : A), x ∈ W ∧ f x = y from
      Exists.intro x (And.intro h2.left.left h2.right)
    done
  · -- Proof that y ∈ image f X
    show y ∈ image f X from
      Exists.intro x (And.intro h2.left.right h2.right)
    done
  done

theorem Theorem_5_5_2_2 {A B : Type} (f : A → B) (W X : Set A)
    (h1 : one_to_one f) : image f (W ∩ X) = image f W ∩ image f X := by
  apply Set.ext
  fix y : B      --Goal: y ∈ image f (W ∩ X) ↔ y ∈ image f W ∩ image f X
  apply Iff.intro
  · -- (→)
    assume h2 : y ∈ image f (W ∩ X)
    show y ∈ image f W ∩ image f X from Theorem_5_5_2_1 f W X h2
    done
  · -- (←)
    assume h2 : y ∈ image f W ∩ image f X  --Goal: y ∈ image f (W ∩ X)
    define at h2                  --h2: y ∈ image f W ∧ y ∈ image f X
    rewrite [simp_image, simp_image] at h2
          --h2: (∃ (x : A), x ∈ W ∧ f x = y) ∧ ∃ (x : A), x ∈ X ∧ f x = y
    obtain (x1 : A) (h3 : x1 ∈ W ∧ f x1 = y) from h2.left
    obtain (x2 : A) (h4 : x2 ∈ X ∧ f x2 = y) from h2.right
    have h5 : f x2 = y := h4.right
    rewrite [←h3.right] at h5  --h5: f x2 = f x1
    define at h1               --h1: ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    have h6 : x2 = x1 := h1 x2 x1 h5
    rewrite [h6] at h4           --h4: x1 ∈ X ∧ f x1 = y
    show y ∈ image f (W ∩ X) from
      Exists.intro x1 (And.intro (And.intro h3.left h4.left) h3.right)
    done
  done

--Warning!  Not all of these examples are correct!
example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    image f (W \ X) = image f W \ image f X := sorry

example {A B : Type} (f : A → B) (W X : Set A) :
    W ⊆ X ↔ image f W ⊆ image f X := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∩ Z) =
        inverse_image f Y ∩ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y ∪ Z) =
        inverse_image f Y ∪ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f  (Y \ Z) =
        inverse_image f Y \ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (Y Z : Set B) :
    Y ⊆ Z ↔ inverse_image f Y ⊆ inverse_image f Z := sorry

example {A B : Type} (f : A → B) (X : Set A) :
    inverse_image f (image f X) = X := sorry

example {A B : Type} (f : A → B) (Y : Set B) :
    image f (inverse_image f Y) = Y := sorry

example {A : Type} (f : A → A) (C : Set A) :
    closed f C → image f C ⊆ C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    image f C ⊆ C → C ⊆ inverse_image f C := sorry

example {A : Type} (f : A → A) (C : Set A) :
    C ⊆ inverse_image f C → closed f C := sorry

example {A B : Type} (f : A → B) (g : B → A) (Y : Set B)
    (h1 : f ∘ g = id) (h2 : g ∘ f = id) :
    inverse_image f Y = image g Y := sorry