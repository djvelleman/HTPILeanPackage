import HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true

/- Definitions -/
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

/- Section 4.2 -/
theorem Theorem_4_2_5_1 {A B : Type}
    (R : Set (A × B)) : inv (inv R) = R := by rfl

theorem Theorem_4_2_5_2 {A B : Type}
    (R : Set (A × B)) : Dom (inv R) = Ran R := by rfl

theorem Theorem_4_2_5_3 {A B : Type}
    (R : Set (A × B)) : Ran (inv R) = Dom R := by rfl

theorem Theorem_4_2_5_4 {A B C D : Type}
    (R : Set (A × B)) (S : Set (B × C)) (T : Set (C × D)) :
    comp T (comp S R) = comp (comp T S) R := by
  apply Set.ext
  fix (a, d) : A × D
  apply Iff.intro
  · -- (→)
    assume h1 : (a, d) ∈ comp T (comp S R)
                     --Goal: (a, d) ∈ comp (comp T S) R
    define           --Goal: ∃ (x : B), (a, x) ∈ R ∧ (x, d) ∈ comp T S
    define at h1     --h1: ∃ (x : C), (a, x) ∈ comp S R ∧ (x, d) ∈ T
    obtain (c : C) (h2 : (a, c) ∈ comp S R ∧ (c, d) ∈ T) from h1
    have h3 : (a, c) ∈ comp S R := h2.left
    define at h3     --h3: ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S
    obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h3
    apply Exists.intro b    --Goal: (a, b) ∈ R ∧ (b, d) ∈ comp T S
    apply And.intro h4.left --Goal: (b, d) ∈ comp T S
    define                  --Goal: ∃ (x : C), (b, x) ∈ S ∧ (x, d) ∈ T
    show ∃ (x : C), (b, x) ∈ S ∧ (x, d) ∈ T from
      Exists.intro c (And.intro h4.right h2.right)
    done
  · -- (←)
    assume h1 : (a, d) ∈ comp (comp T S) R
    define; define at h1
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, d) ∈ comp T S) from h1
    have h3 : (b, d) ∈ comp T S := h2.right
    define at h3
    obtain (c : C) (h4 : (b, c) ∈ S ∧ (c, d) ∈ T) from h3
    apply Exists.intro c
    apply And.intro _ h4.right
    define
    show ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S from
      Exists.intro b (And.intro h2.left h4.left)
    done
  done

theorem simp_inv {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

theorem Theorem_4_2_5_5 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by
  apply Set.ext
  fix (c, a) : C × A
  apply Iff.intro
  · -- (→)
    assume h1 : (c, a) ∈ inv (comp S R)
                         --Goal: (c, a) ∈ comp (inv R) (inv S)
    define at h1         --h1: ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S
    define               --Goal: ∃ (x : B), (c, x) ∈ inv S ∧ (x, a) ∈ inv R
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S) from h1
    apply Exists.intro b         --Goal: (c, b) ∈ inv S ∧ (b, a) ∈ inv R
    rewrite [simp_inv, simp_inv] --Goal: (b, c) ∈ S ∧ (a, b) ∈ R
    show (b, c) ∈ S ∧ (a, b) ∈ R from And.intro h2.right h2.left
    done
  · -- (←)
    assume h1 : (c, a) ∈ comp (inv R) (inv S)
    define at h1
    define
    obtain (b : B) (h2 : (c, b) ∈ inv S ∧ (b, a) ∈ inv R) from h1
    apply Exists.intro b
    rewrite [simp_inv, simp_inv] at h2
    show (a, b) ∈ R ∧ (b, c) ∈ S from And.intro h2.right h2.left
    done
  done

-- Exercises
-- 1.
theorem Exercise_4_2_9a {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom (comp S R) ⊆ Dom R := sorry

-- 2.
theorem Exercise_4_2_9b {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R ⊆ Dom S → Dom (comp S R) = Dom R := sorry

-- 3.
--Fill in the blank to get a correct theorem and then prove the theorem
theorem Exercise_4_2_9c {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : ___ → Ran (comp S R) = Ran S := sorry

-- 4.
theorem Exercise_4_2_12a {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    (comp S R) \ (comp T R) ⊆ comp (S \ T) R := sorry

-- 5.
--You won't be able to complete this proof
theorem Exercise_4_2_12b {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S \ T) R ⊆ (comp S R) \ (comp T R) := sorry

-- 6.
--You might not be able to complete this proof
theorem Exercise_4_2_14c {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∩ T) R = (comp S R) ∩ (comp T R) := sorry

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_2_14d {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∪ T) R = (comp S R) ∪ (comp T R) := sorry

/- Section 4.3 -/
theorem simp_ext {A B : Type} (R : Rel A B) (a : A) (b : B) :
    (a, b) ∈ extension R ↔ R a b := by rfl

theorem Theorem_4_3_4_2 {A : Type} (R : BinRel A) :
    symmetric R ↔ extension R = inv (extension R) := by
  apply Iff.intro
  · -- (→)
    assume h1 : symmetric R
    define at h1             --h1: ∀ (x y : A), R x y → R y x
    apply Set.ext
    fix (a, b) : A × A
    show (a, b) ∈ extension R ↔ (a, b) ∈ inv (extension R) from
      calc (a, b) ∈ extension R
          ↔ R a b := by rfl
        _ ↔ R b a := Iff.intro (h1 a b) (h1 b a)
        _ ↔ (a, b) ∈ inv (extension R) := by rfl
    done
  · -- (←)
    assume h1 : extension R = inv (extension R)
    define                   --Goal: ∀ (x y : A), R x y → R y x
    fix a : A; fix b : A
    assume h2 : R a b        --Goal: R b a
    rewrite [←simp_ext R, h1, simp_inv, simp_ext] at h2
    show R b a from h2
    done
  done

theorem simp_relFromExt {A B : Type}
    (R : Set (A × B)) (a : A) (b : B) :
    relFromExt R a b ↔ (a, b) ∈ R := by rfl

example {A B : Type} (R : Rel A B) :
    relFromExt (extension R) = R := by rfl

example {A B : Type} (R : Set (A × B)) :
    extension (relFromExt R) = R := by rfl

-- Exercises
-- 1.
example :
    elementhood Int 6 { n : Int | ∃ (k : Int), n = 2 * k } := sorry

-- 2.
theorem Theorem_4_3_4_1 {A : Type} (R : BinRel A) :
    reflexive R ↔ { (x, y) : A × A | x = y } ⊆ extension R := sorry

-- 3.
theorem Theorem_4_3_4_3 {A : Type} (R : BinRel A) :
    transitive R ↔
      comp (extension R) (extension R) ⊆ extension R := sorry

-- 4.
theorem Exercise_4_3_12a {A : Type} (R : BinRel A) (h1 : reflexive R) :
    reflexive (relFromExt (inv (extension R))) := sorry

-- 5.
theorem Exercise_4_3_12c {A : Type} (R : BinRel A) (h1 : transitive R) :
    transitive (relFromExt (inv (extension R))) := sorry

-- 6.
theorem Exercise_4_3_18 {A : Type}
    (R S : BinRel A) (h1 : transitive R) (h2 : transitive S)
    (h3 : comp (extension S) (extension R) ⊆
      comp (extension R) (extension S)) :
    transitive (relFromExt (comp (extension R) (extension S))) := sorry

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_3_13b {A : Type}
    (R1 R2 : BinRel A) (h1 : symmetric R1) (h2 : symmetric R2) :
    symmetric (relFromExt ((extension R1) ∪ (extension R2))) := sorry

-- 8.
--You might not be able to complete this proof
theorem Exercise_4_3_13c {A : Type}
    (R1 R2 : BinRel A) (h1 : transitive R1) (h2 : transitive R2) :
    transitive (relFromExt ((extension R1) ∪ (extension R2))) := sorry

/- Section 4.4 -/
theorem Theorem_4_4_6_2 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    minimalElt R b B ∧ ∀ (c : A), minimalElt R c B → b = c := by
  define at h1     --h1: reflexive R ∧ transitive R ∧ antisymmetric R
  define at h2     --h2: b ∈ B ∧ ∀ (x : A), x ∈ B → R b x
  apply And.intro
  · -- Proof that b is minimal
    define           --Goal: b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
    apply And.intro h2.left
    quant_neg        --Goal: ∀ (x : A), ¬(x ∈ B ∧ R x b ∧ x ≠ b)
    fix x : A
    demorgan         --Goal: ¬x ∈ B ∨ ¬(R x b ∧ x ≠ b)
    or_right with h3 --h3: x ∈ B; Goal: ¬(R x b ∧ x ≠ b)
    demorgan         --Goal: ¬R x b ∨ x = b
    or_right with h4 --h4: R x b; Goal: x = b
    have h5 : R b x := h2.right x h3
    have h6 : antisymmetric R := h1.right.right
    define at h6     --h6: ∀ (x y : A), R x y → R y x → x = y
    show x = b from h6 x b h4 h5
    done
  · -- Proof that b is only minimal element
    fix c : A
    assume h3 : minimalElt R c B
    define at h3    --h3: c ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c
    contradict h3.right with h4
                  --h4: ¬b = c; Goal: ∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c
    have h5 : R b c := h2.right c h3.left
    show ∃ (x : A), x ∈ B ∧ R x c ∧ x ≠ c from
      Exists.intro b (And.intro h2.left (And.intro h5 h4))
    done
  done

theorem Theorem_4_4_6_3 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : total_order R) (h2 : minimalElt R b B) : smallestElt R b B := by
  define at h1         --h1: partial_order R ∧ ∀ (x y : A), R x y ∨ R y x
  define at h2         --h2: b ∈ B ∧ ¬∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b
  define               --Goal: b ∈ B ∧ ∀ (x : A), x ∈ B → R b x
  apply And.intro h2.left  --Goal: ∀ (x : A), x ∈ B → R b x
  fix x : A
  assume h3 : x ∈ B        --Goal: R b x
  by_cases h4 : x = b
  · -- Case 1. h4: x = b
    rewrite [h4]             --Goal: R b b
    have h5 : partial_order R := h1.left
    define at h5
    have h6 : reflexive R := h5.left
    define at h6
    show R b b from h6 b
    done
  · -- Case 2. h4: x ≠ b
    have h5 : ∀ (x y : A), R x y ∨ R y x := h1.right
    have h6 : R x b ∨ R b x := h5 x b
    have h7 : ¬R x b := by
      contradict h2.right with h8
      show ∃ (x : A), x ∈ B ∧ R x b ∧ x ≠ b from
        Exists.intro x (And.intro h3 (And.intro h8 h4))
      done
    disj_syll h6 h7
    show R b x from h6
    done
  done

-- Exercises
-- 1.
theorem Example_4_4_3_1 {A : Type} : partial_order (sub A) := sorry

-- 2.
theorem Theorem_4_4_6_1 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    ∀ (c : A), smallestElt R c B → b = c := sorry

-- 3.
--If F is a set of sets, then ⋃₀ F is the lub of F in the subset ordering
theorem Theorem_4_4_11 {A : Type} (F : Set (Set A)) :
    lub (sub A) (⋃₀ F) F := sorry

-- 4.
theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := sorry

-- 5.
theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := sorry

-- 6.
theorem Exercise_4_4_15a {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    smallestElt R1 b B → smallestElt R2 b B := sorry

-- 7.
theorem Exercise_4_4_15b {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    minimalElt R2 b B → minimalElt R1 b B := sorry

-- 8.
theorem Exercise_4_4_18a {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (h1 : partial_order R)
    (h2 : ∀ x ∈ B1, ∃ y ∈ B2, R x y) (h3 : ∀ x ∈ B2, ∃ y ∈ B1, R x y) :
    ∀ (x : A), upperBd R x B1 ↔ upperBd R x B2 := sorry

-- 9.
theorem Exercise_4_4_22 {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (x1 x2 : A)
    (h1 : lub R x1 B1) (h2 : lub R x2 B2) :
    B1 ⊆ B2 → R x1 x2 := sorry

-- 10.
theorem Exercise_4_4_24 (A : Type) (R : Set (A × A)) :
    smallestElt (sub (A × A)) (R ∪ (inv R))
    { T : Set (A × A) | R ⊆ T ∧ symmetric (relFromExt T) } := sorry

/- Section 4.5 -/
lemma Lemma_4_5_5_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ equivClass R x := by
  fix x : A
  define           --Goal: R x x
  define at h      --h: reflexive R ∧ symmetric R ∧ transitive R
  have href : reflexive R := h.left
  show R x x from href x
  done

lemma Lemma_4_5_5_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x y : A), y ∈ equivClass R x ↔
      equivClass R y = equivClass R x := by
  have hsymm : symmetric R := h.right.left
  have htrans : transitive R := h.right.right
  fix x : A; fix y : A
  apply Iff.intro
  · -- (→)
    assume h2 : y ∈ equivClass R x --Goal: equivClass R y = equivClass R x
    define at h2                   --h2: R y x
    apply Set.ext
    fix z : A
    apply Iff.intro
    · -- Proof that z ∈ equivClass R y → z ∈ equivClass R x
      assume h3 : z ∈ equivClass R y
      define                         --Goal: R z x
      define at h3                   --h3: R z y
      show R z x from htrans z y x h3 h2
      done
    · -- Proof that z ∈ equivClass R x → z ∈ equivClass R y
      assume h3 : z ∈ equivClass R x
      define                         --Goal: R z y
      define at h3                   --h3: R z x
      have h4 : R x y := hsymm y x h2
      show R z y from htrans z x y h3 h4
      done
    done
  · -- (←)
    assume h2 : equivClass R y = equivClass R x --Goal: y ∈ equivClass R x
    rewrite [←h2]                  --Goal: y ∈ equivClass R y
    show y ∈ equivClass R y from Lemma_4_5_5_1 R h y
    done
  done

lemma Theorem_4_5_4_part_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ ⋃₀ (mod A R) := by
  fix x : A
  define        --Goal: ∃ (t : Set A), t ∈ mod A R ∧ x ∈ t
  apply Exists.intro (equivClass R x)
  apply And.intro _ (Lemma_4_5_5_1 R h x)
                --Goal: equivClass R x ∈ mod A R
  define        --Goal: ∃ (x_1 : A), equivClass R x_1 = equivClass R x
  apply Exists.intro x
  rfl

lemma Theorem_4_5_4_part_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    pairwise_disjoint (mod A R) := by
  define
  fix X : Set A
  assume h2 : X ∈ mod A R
  fix Y : Set A
  assume h3 : Y ∈ mod A R           --Goal: X ≠ Y → empty (X ∩ Y)
  define at h2; define at h3
  obtain (x : A) (h4 : equivClass R x = X) from h2
  obtain (y : A) (h5 : equivClass R y = Y) from h3
  contrapos
  assume h6 : ∃ (x : A), x ∈ X ∩ Y  --Goal: X = Y
  obtain (z : A) (h7 : z ∈ X ∩ Y) from h6
  define at h7
  rewrite [←h4, ←h5] at h7 --h7: z ∈ equivClass R x ∧ z ∈ equivClass R y
  have h8 : equivClass R z = equivClass R x :=
    (Lemma_4_5_5_2 R h x z).ltr h7.left
  have h9 : equivClass R z = equivClass R y :=
    (Lemma_4_5_5_2 R h y z).ltr h7.right
  show X = Y from
    calc X
        = equivClass R x := h4.symm
      _ = equivClass R z := h8.symm
      _ = equivClass R y := h9
      _ = Y              := h5
  done

lemma Theorem_4_5_4_part_3 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ¬empty X := by
  fix X : Set A
  assume h2 : X ∈ mod A R  --Goal: ¬empty X
  define; double_neg       --Goal: ∃ (x : A), x ∈ X
  define at h2             --h2: ∃ (x : A), equivClass R x = X
  obtain (x : A) (h3 : equivClass R x = X) from h2
  rewrite [←h3]
  show ∃ (x_1 : A), x_1 ∈ equivClass R x from
    Exists.intro x (Lemma_4_5_5_1 R h x)
  done

theorem Theorem_4_5_4 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    partition (mod A R) := And.intro (Theorem_4_5_4_part_1 R h)
      (And.intro (Theorem_4_5_4_part_2 R h) (Theorem_4_5_4_part_3 R h))

lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F):
    reflexive (EqRelFromPart F) := sorry
  
lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F):
    symmetric (EqRelFromPart F) := sorry

lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F):
    transitive (EqRelFromPart F) := sorry

lemma Lemma_4_5_7 {A : Type} (F : Set (Set A)) (h : partition F) :
    equiv_rel (EqRelFromPart F) := And.intro (Lemma_4_5_7_ref F h)
      (And.intro (Lemma_4_5_7_symm F h) (Lemma_4_5_7_trans F h))

lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

theorem Theorem_4_5_6 {A : Type} (F : Set (Set A)) (h: partition F) :
    ∃ (R : BinRel A), equiv_rel R ∧ mod A R = F := by
  let R : BinRel A := EqRelFromPart F
  apply Exists.intro R              --Goal: equiv_rel R ∧ mod A R = F
  apply And.intro (Lemma_4_5_7 F h) --Goal: mod A R = F
  apply Set.ext
  fix X : Set A                     --Goal:  X ∈ mod A R ↔ X ∈ F
  apply Iff.intro
  · -- (→)
    assume h2 : X ∈ mod A R           --Goal: X ∈ F
    define at h2                      --h2: ∃ (x : A), equivClass R x = X
    obtain (x : A) (h3 : equivClass R x = X) from h2
    have h4 : x ∈ ⋃₀ F := h.left x
    define at h4
    obtain (Y : Set A) (h5 : Y ∈ F ∧ x ∈ Y) from h4
    have h6 : equivClass R x = Y :=
      Lemma_4_5_8 F h Y h5.left x h5.right
    rewrite [←h3, h6]
    show Y ∈ F from h5.left
    done
  · -- (←)
    assume h2 : X ∈ F                 --Goal: X ∈ mod A R
    have h3 : ¬empty X := h.right.right X h2
    define at h3; double_neg at h3    --h3: ∃ (x : A), x ∈ X
    obtain (x : A) (h4 : x ∈ X) from h3
    define                       --Goal: ∃ (x : A), equivClass R x = X
    show ∃ (x : A), equivClass R x = X from
      Exists.intro x (Lemma_4_5_8 F h X h2 x h4)
    done
  done

-- Exercises
-- 1.
lemma overlap_implies_equal_ex {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

-- 2.
lemma Lemma_4_5_7_ref_ex {A : Type} (F : Set (Set A)) (h : partition F):
    reflexive (EqRelFromPart F) := sorry

-- 3.
lemma Lemma_4_5_7_symm_ex {A : Type} (F : Set (Set A)) (h : partition F):
    symmetric (EqRelFromPart F) := sorry

-- 4.
lemma Lemma_4_5_7_trans_ex {A : Type} (F : Set (Set A)) (h : partition F):
    transitive (EqRelFromPart F) := sorry

-- 5.
lemma Lemma_4_5_8_ex {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

-- 6.
lemma elt_mod_equiv_class_of_elt
    {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ∀ x ∈ X, equivClass R x = X := sorry

-- Definitions for next three exercises:
def dot {A : Type} (F G : Set (Set A)) : Set (Set A) :=
    { Z : Set A | ¬empty Z ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y }

def conj {A : Type} (R S : BinRel A) (x y : A) : Prop :=
    R x y ∧ S x y

-- 7.
theorem Exercise_4_5_20a {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    equiv_rel (conj R S) := sorry

-- 8.
theorem Exercise_4_5_20b {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    ∀ (x : A), equivClass (conj R S) x =
      equivClass R x ∩ equivClass S x := sorry

-- 9.
theorem Exercise_4_5_20c {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    mod A (conj R S) = dot (mod A R) (mod A S) := sorry

-- 10.
def equiv_mod (m x y : Int) : Prop := m ∣ (x - y)

theorem Theorem_4_5_10 : ∀ (m : Int), equiv_rel (equiv_mod m) := sorry
