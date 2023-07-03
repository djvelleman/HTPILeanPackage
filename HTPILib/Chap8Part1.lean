import Chap5
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Definitions -/
def invRel {A B : Type} (R : Rel A B) : Rel B A :=
  RelFromExt (inv (extension R))

def rel_within {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
  ∀ ⦃x : A⦄ ⦃y : B⦄, R x y → x ∈ X ∧ y ∈ Y

def fcnl_on {A B : Type} (R : Rel A B) (X : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ X → ∃! (y : B), R x y

def matching {A B : Type} (R : Rel A B) (X : Set A) (Y : Set B) : Prop :=
  rel_within R X Y ∧ fcnl_on R X ∧ fcnl_on (invRel R) Y

def equinum {A B : Type} (X : Set A) (Y : Set B) : Prop :=
  ∃ (R : Rel A B), matching R X Y

notation:50  X:50 " ∼ " Y:50 => equinum X Y

def RelWithinFromFunc {A B : Type} (f : A → B) (X : Set A)
  (x : A) (y : B) : Prop := x ∈ X ∧ f x = y

def one_one_on {A B : Type} (f : A → B) (X : Set A) : Prop :=
  ∀ ⦃x1 x2 : A⦄, x1 ∈ X → x2 ∈ X → f x1 = f x2 → x1 = x2

def Univ (A : Type) : Set A := { x : A | True }

def compRel {A B C : Type} (S : Rel B C) (R : Rel A B) : Rel A C :=
  RelFromExt (comp (extension S) (extension R))

def I (n : Nat) : Set Nat := { k : Nat | k < n }

def finite {A : Type} (X : Set A) : Prop :=
  ∃ (n : Nat), I n ∼ X

def denum {A : Type} (X : Set A) : Prop :=
  Univ Nat ∼ X

def ctble {A : Type} (X : Set A) : Prop :=
  finite X ∨ denum X

def numElts {A : Type} (X : Set A) (n : Nat) : Prop := I n ∼ X

def emptyRel (A B : Type) (x : A) (y : B) : Prop := False

def remove_one {A B : Type} (R : Rel A B) (u : A) (v : B)
  (x : A) (y : B) : Prop := x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y))

def one_match {A B : Type} (a : A) (b : B)
  (x : A) (y : B) : Prop := x = a ∧ y = b

/- Section 8.1 -/
lemma invRel_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    invRel R b a ↔ R a b := by rfl

theorem equinum_image {A B : Type} {X : Set A} {Y : Set B} {f : A → B}
    (h1 : one_one_on f X) (h2 : image f X = Y) : X ∼ Y := by
  rewrite [←h2]
  define   --Goal : ∃ (R : Rel A B), matching R X (image f X)
  set R : Rel A B := RelWithinFromFunc f X
  apply Exists.intro R
  define   --Goal : rel_within R X (image f X) ∧
           --fcnl_on R X ∧ fcnl_on (invRel R) (image f X)
  apply And.intro
  · -- Proof of rel_within
    define --Goal : ∀ ⦃x : A⦄ ⦃y : B⦄, R x y → x ∈ X ∧ y ∈ image f X
    fix x : A; fix y : B
    assume h3 : R x y  --Goal : x ∈ X ∧ y ∈ image f X
    define at h3       --h3 : x ∈ X ∧ f x = y
    apply And.intro h3.left
    define
    show ∃ (x : A), x ∈ X ∧ f x = y from Exists.intro x h3
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R X
      define  --Goal : ∀ ⦃x : A⦄, x ∈ X → ∃! (y : B), R x y
      fix x : A
      assume h3 : x ∈ X
      exists_unique
      · -- Existence
        apply Exists.intro (f x)
        define  --Goal : x ∈ X ∧ f x = f x
        apply And.intro h3
        rfl
        done
      · -- Uniqueness
        fix y1 : B; fix y2 : B
        assume h4 : R x y1
        assume h5 : R x y2   --Goal : y1 = y2
        define at h4; define at h5
          --h4 : x ∈ X ∧ f x = y1;  h5 : x ∈ X ∧ f x = y2
        rewrite [h4.right] at h5
        show y1 = y2 from h5.right
        done
      done
    · -- Proof of fcnl_on (invRel R) (image f X)
      define  --Goal : ∀ ⦃x : B⦄, x ∈ image f X → ∃! (y : A), invRel R x y
      fix y : B
      assume h3 : y ∈ image f X
      obtain (x : A) (h4 : x ∈ X ∧ f x = y) from h3
      exists_unique
      · -- Existence
        apply Exists.intro x
        define
        show x ∈ X ∧ f x = y from h4
        done
      · -- Uniqueness
        fix x1 : A; fix x2 : A
        assume h5 : invRel R y x1
        assume h6 : invRel R y x2
        define at h5; define at h6
          --h5 : x1 ∈ X ∧ f x1 = y;  h6 : x2 ∈ X ∧ f x2 = y
        rewrite [←h6.right] at h5
        show x1 = x2 from h1 h5.left h6.left h5.right
        done
      done
    done
  done

lemma id_one_one_on {A : Type} (X : Set A) : one_one_on id X := by
  define
  fix x1 : A; fix x2 : A
  assume h1 : x1 ∈ X; assume h2 : x2 ∈ X
  assume h3 : id x1 = id x2
  show x1 = x2 from h3
  done

lemma image_id {A : Type} (X : Set A) : image id X = X := by
  apply Set.ext
  fix x : A
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ image id X
    obtain (y : A) (h2 : y ∈ X ∧ id y = x) from h1
    rewrite [←h2.right]
    show id y ∈ X from h2.left
    done
  · -- (←)
    assume h1 : x ∈ X
    apply Exists.intro x  --Goal : x ∈ X ∧ id x = x
    apply And.intro h1
    rfl
    done
  done

theorem Theorem_8_1_3_1 {A : Type} (X : Set A) : X ∼ X :=
  equinum_image (id_one_one_on X) (image_id X)

lemma inv_inv {A B : Type} (R : Rel A B) : invRel (invRel R) = R := by rfl

lemma inv_match {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B}
    (h : matching R X Y) : matching (invRel R) Y X := by
  define       --Goal : rel_within (invRel R) Y X ∧
               --fcnl_on (invRel R) Y ∧ fcnl_on (invRel (invRel R)) X
  define at h  --h : rel_within R X Y ∧ fcnl_on R X ∧ fcnl_on (invRel R) Y
  apply And.intro
  · -- Proof that rel_within R Y X
    define     --Goal : ∀ ⦃x : B⦄ ⦃y : A⦄, invRel R x y → x ∈ Y ∧ y ∈ X
    fix y : B; fix x : A
    assume h1 : invRel R y x
    define at h1  --h1 : R x y
    have h2 : x ∈ X ∧ y ∈ Y := h.left h1
    show y ∈ Y ∧ x ∈ X from And.intro h2.right h2.left
    done
  · -- proof that fcnl_on (inv R) Y ∧ fcnl_on (inv (inv R)) X
    rewrite [inv_inv]
    show fcnl_on (invRel R) Y ∧ fcnl_on R X from
      And.intro h.right.right h.right.left
    done
  done

theorem Theorem_8_1_3_2 {A B : Type} {X : Set A} {Y : Set B}
    (h : X ∼ Y) : Y ∼ X := by
  obtain (R : Rel A B) (h1 : matching R X Y) from h
  apply Exists.intro (invRel R)
  show matching (invRel R) Y X from inv_match h1
  done

lemma fcnl_exists {A B : Type} {R : Rel A B} {X : Set A} {x : A}
    (h1 : fcnl_on R X) (h2 : x ∈ X) : ∃ (y : B), R x y := by
  define at h1
  obtain (y : B) (h3 : R x y)
    (h4 : ∀ (y_1 y_2 : B), R x y_1 → R x y_2 → y_1 = y_2) from h1 h2
  show ∃ (y : B), R x y from Exists.intro y h3
  done

lemma fcnl_unique {A B : Type}
    {R : Rel A B} {X : Set A} {x : A} {y1 y2 : B} (h1 : fcnl_on R X)
    (h2 : x ∈ X) (h3 : R x y1) (h4 : R x y2) : y1 = y2 := by
  define at h1
  obtain (z : B) (h5 : R x z)
    (h6 : ∀ (y_1 y_2 : B), R x y_1 → R x y_2 → y_1 = y_2) from h1 h2
  show y1 = y2 from h6 y1 y2 h3 h4
  done

lemma compRel_def {A B C : Type}
    (S : Rel B C) (R : Rel A B) (a : A) (c : C) :
    compRel S R a c ↔ ∃ (x : B), R a x ∧ S x c := by rfl

lemma inv_comp {A B C : Type} (R : Rel A B) (S : Rel B C) :
    invRel (compRel S R) = compRel (invRel R) (invRel S) := 
  calc invRel (compRel S R)
    _ = RelFromExt (inv (comp (extension S) (extension R))) := by rfl
    _ = RelFromExt (comp (inv (extension R)) (inv (extension S))) :=
        by rw [Theorem_4_2_5_5]
    _ = compRel (invRel R) (invRel S) := by rfl

lemma comp_fcnl {A B C : Type} {R : Rel A B} {S : Rel B C}
    {X : Set A} {Y : Set B} {Z : Set C} (h1 : matching R X Y)
    (h2 : matching S Y Z) : fcnl_on (compRel S R) X := by
  define; define at h1; define at h2
  fix a : A
  assume h3 : a ∈ X
  obtain (b : B) (h4 : R a b) from fcnl_exists h1.right.left h3
  have h5 : a ∈ X ∧ b ∈ Y := h1.left h4
  obtain (c : C) (h6 : S b c) from fcnl_exists h2.right.left h5.right
  exists_unique
  · -- Existence
    apply Exists.intro c
    rewrite [compRel_def]
    show ∃ (x : B), R a x ∧ S x c from Exists.intro b (And.intro h4 h6)
    done
  · -- Uniqueness
    fix c1 : C; fix c2 : C
    assume h7 : compRel S R a c1
    assume h8 : compRel S R a c2    --Goal : c1 = c2
    rewrite [compRel_def] at h7
    rewrite [compRel_def] at h8
    obtain (b1 : B) (h9 : R a b1 ∧ S b1 c1) from h7
    obtain (b2 : B) (h10 : R a b2 ∧ S b2 c2) from h8
    have h11 : b1 = b := fcnl_unique h1.right.left h3 h9.left h4
    have h12 : b2 = b := fcnl_unique h1.right.left h3 h10.left h4
    rewrite [h11] at h9
    rewrite [h12] at h10
    show c1 = c2 from
      fcnl_unique h2.right.left h5.right h9.right h10.right
    done
  done

lemma comp_match {A B C : Type} {R : Rel A B} {S : Rel B C}
    {X : Set A} {Y : Set B} {Z : Set C} (h1 : matching R X Y)
    (h2 : matching S Y Z) : matching (compRel S R) X Z := by
  define
  apply And.intro
  · -- Proof of rel_within (compRel S R) X Z
    define
    fix a : A; fix c : C
    assume h3 : compRel S R a c
    rewrite [compRel_def] at h3
    obtain (b : B) (h4 : R a b ∧ S b c) from h3
    have h5 : a ∈ X ∧ b ∈ Y := h1.left h4.left
    have h6 : b ∈ Y ∧ c ∈ Z := h2.left h4.right
    show a ∈ X ∧ c ∈ Z from And.intro h5.left h6.right
    done
  · -- Proof of fcnl_on statements
    apply And.intro
    · -- Proof of fcnl_on (compRel S R) X
      show fcnl_on (compRel S R) X from comp_fcnl h1 h2
      done
    · -- Proof of fcnl_on (invRel (compRel S R)) Z
      rewrite [inv_comp]
      have h3 : matching (invRel R) Y X := inv_match h1
      have h4 : matching (invRel S) Z Y := inv_match h2
      show fcnl_on (compRel (invRel R) (invRel S)) Z from comp_fcnl h4 h3
      done
    done
  done

theorem Theorem_8_1_3_3 {A B C : Type} {X : Set A} {Y : Set B} {Z : Set C}
    (h1 : X ∼ Y) (h2 : Y ∼ Z) : X ∼ Z := by
  obtain (R : Rel A B) (h3 : matching R X Y) from h1
  obtain (S : Rel B C) (h4 : matching S Y Z) from h2
  apply Exists.intro (compRel S R)
  show matching (compRel S R) X Z from comp_match h3 h4
  done

lemma I_def (k n : Nat) : k ∈ I n ↔ k < n := by rfl

lemma denum_def {A : Type} (X : Set A) : denum X ↔ Univ Nat ∼ X := by rfl

/- Section 8.1½ -/
lemma numElts_def {A : Type} (X : Set A) (n : Nat) :
    numElts X n ↔ I n ∼ X := by rfl

lemma fcnl_on_empty {A B : Type}
    (R : Rel A B) {X : Set A} (h1 : empty X) : fcnl_on R X := by
  define
  fix a : A
  assume h2 : a ∈ X      --Goal : ∃! (y : B), R a y
  contradict h1 with h3  --Goal : ∃ (x : A), x ∈ X
  show ∃ (x : A), x ∈ X from Exists.intro a h2
  done

lemma empty_match {A B : Type} {X : Set A} {Y : Set B}
    (h1 : empty X) (h2 : empty Y) : matching (emptyRel A B) X Y := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a : A; fix b : B
    assume h3 : emptyRel A B a b   --Goal : a ∈ X ∧ b ∈ Y
    by_contra h4                   --Goal : False
    define at h3
    show False from h3
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on emptyRel
      show fcnl_on (emptyRel A B) X from fcnl_on_empty (emptyRel A B) h1
      done
    · -- Proof of fcnl_on (invRel emptyRel)
      show fcnl_on (invRel (emptyRel A B)) Y from
        fcnl_on_empty (invRel (emptyRel A B)) h2
      done
  done

lemma I_0_empty : empty (I 0) := by
  define
  by_contra h1    --h1 : ∃ (x : Nat), x ∈ I 0
  obtain (x : Nat) (h2 : x ∈ I 0) from h1
  define at h2    --h2 : x < 0
  linarith
  done

theorem zero_elts_iff_empty {A : Type} (X : Set A) :
    numElts X 0 ↔ empty X := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts X 0
    define
    by_contra h2         --h2 : ∃ (x : A), x ∈ X
    obtain (x : A) (h3 : x ∈ X) from h2
    define at h1
    obtain (R : Rel Nat A) (h4 : matching R (I 0) X) from h1
    define at h4
      --h4 : rel_within R (I 0) X ∧ fcnl_on R (I 0) ∧ fcnl_on (invRel R) X
    obtain (j : Nat) (h5 : invRel R x j) from
      fcnl_exists h4.right.right h3
    define at h5         --h5 : R j x
    have h6 : j ∈ I 0 ∧ x ∈ X := h4.left h5
    contradict I_0_empty --Goal : ∃ (x : Nat), x ∈ I 0
    show ∃ (x : Nat), x ∈ I 0 from Exists.intro j h6.left
    done
  · -- (←)
    assume h1 : empty X
    show ∃ (R : Rel Nat A), matching R (I 0) X from
      Exists.intro (emptyRel Nat A) (empty_match I_0_empty h1)
    done
  done

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X := by
  define at h1
  obtain (R : Rel Nat A) (h3 : matching R (I n) X) from h1
  define at h3
  have h4 : 0 ∈ I n := h2
  obtain (x : A) (h5 : R 0 x) from fcnl_exists h3.right.left h4
  have h6 : 0 ∈ I n ∧ x ∈ X := h3.left h5
  show ∃ (x : A), x ∈ X from Exists.intro x h6.right
  done

theorem relext {A B : Type} {R S : Rel A B}
    (h : ∀ (a : A) (b : B), R a b ↔ S a b) : R = S := by
  have h2 : extension R = extension S := by
    apply Set.ext
    fix (a, b) : A × B --Goal : (a, b) ∈ extension R ↔ (a, b) ∈ extension S
    rewrite [ext_def, ext_def]  --Goal : R a b ↔ S a b
    show R a b ↔ S a b from h a b
    done
  show R = S from
    calc R
      _ = RelFromExt (extension R) := by rfl
      _ = RelFromExt (extension S) := by rw [h2]
      _ = S := by rfl
  done

lemma remove_one_def {A B : Type} (R : Rel A B) (u x : A) (v y : B) :
    remove_one R u v x y ↔
      x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y)) := by rfl

lemma remove_one_rel_within {A B : Type}
    {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {y v : B}
    (h1 : matching R X Y) (h2 : remove_one R u v x y) :
    x ∈ X \ {u} ∧ y ∈ Y \ {v} := by
  define at h1  --h1 : rel_within R X Y ∧ fcnl_on R X ∧ fcnl_on (invRel R) Y
  define at h2  --h2 : x ≠ u ∧ y ≠ v ∧ (R x y ∨ R x v ∧ R u y)
  have h3 : x ∈ X ∧ y ∈ Y := by
    by_cases on h2.right.right with h3
    · -- Case 1. h3 : R x y
      show x ∈ X ∧ y ∈ Y from h1.left h3
      done
    · -- Case 2. h3 : R x v ∧ R u y
      have h4 : x ∈ X ∧ v ∈ Y := h1.left h3.left
      have h5 : u ∈ X ∧ y ∈ Y := h1.left h3.right
      show x ∈ X ∧ y ∈ Y from And.intro h4.left h5.right
      done
    done
  show x ∈ X \ {u} ∧ y ∈ Y \ {v} from
    And.intro (And.intro h3.left h2.left) (And.intro h3.right h2.right.left)
  done

lemma remove_one_inv {A B : Type} (R : Rel A B) (u : A) (v : B) :
    invRel (remove_one R u v) = remove_one (invRel R) v u := by
  apply relext
  fix y : B; fix x : A
    --Goal : invRel (remove_one R u v) y x ↔ remove_one (invRel R) v u y x
  rewrite [invRel_def, remove_one_def, remove_one_def]
  rewrite [invRel_def, invRel_def, invRel_def]
  rewrite [←and_assoc, ←and_assoc]
    --Goal : (x ≠ u ∧ y ≠ v) ∧ (R x y ∨ R x v ∧ R u y) ↔
    --       (y ≠ v ∧ x ≠ u) ∧ (R x y ∨ R u y ∧ R x v)
  have h1 : x ≠ u ∧ y ≠ v ↔ y ≠ v ∧ x ≠ u := and_comm
  have h2 : R x v ∧ R u y ↔ R u y ∧ R x v := and_comm
  rewrite [h1, h2]
  rfl
  done

lemma remove_one_iff {A B : Type}
    {X : Set A} {Y : Set B} {R : Rel A B} (h1 : matching R X Y)
    {u : A} (h2 : u ∈ X) (v : B) {x : A} (h3 : x ∈ X \ {u}) :
    ∃ (w : A), w ∈ X ∧ ∀ (y : B), remove_one R u v x y ↔ R w y := sorry

theorem remove_one_fcnl {A B : Type}
    {R : Rel A B} {X : Set A} {Y : Set B} {u : A}
    (h1 : matching R X Y) (h2 : u ∈ X) (v : B) :
    fcnl_on (remove_one R u v) (X \ {u}) := by
  define
  fix x : A
  assume h3 : x ∈ X \ {u}  --Goal : ∃! (y : B), remove_one R u v x y
  obtain (w : A) (h4 : w ∈ X ∧ ∀ (y : B),
    remove_one R u v x y ↔ R w y) from remove_one_iff h1 h2 v h3
  define at h1
  exists_unique
  · -- Existence
    obtain (y : B) (h5 : R w y) from fcnl_exists h1.right.left h4.left
    apply Exists.intro y
    rewrite [h4.right]
    show R w y from h5
    done
  · -- Uniqueness
    fix y1 : B; fix y2 : B
    rewrite [h4.right, h4.right]
    assume h5 : R w y1
    assume h6 : R w y2
    show y1 = y2 from fcnl_unique h1.right.left h4.left h5 h6
    done
  done

theorem remove_one_match {A B : Type}
    {R : Rel A B} {X : Set A} {Y : Set B} {u : A} {v : B}
    (h1 : matching R X Y) (h2 : u ∈ X) (h3 : v ∈ Y) :
    matching (remove_one R u v) (X \ {u}) (Y \ {v}) := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix x : A; fix y : B
    assume h4 : remove_one R u v x y
    show x ∈ X \ {u} ∧ y ∈ Y \ {v} from remove_one_rel_within h1 h4
    done
  · -- Proof of fcnl_ons
    apply And.intro (remove_one_fcnl h1 h2 v)
    rewrite [remove_one_inv]
    show fcnl_on (remove_one (invRel R) v u) (Y \ {v}) from
      remove_one_fcnl (inv_match h1) h3 u
  done

theorem remove_one_equinum {A B : Type}
    {X : Set A} {Y : Set B} {u : A} {v : B}
    (h1 : X ∼ Y) (h2 : u ∈ X) (h3 : v ∈ Y) : X \ {u} ∼ Y \ {v} := by
  define
  obtain (R : Rel A B) (h4 : matching R X Y) from h1
  apply Exists.intro (remove_one R u v)
  show matching (remove_one R u v) (X \ {u}) (Y \ {v}) from
    remove_one_match h4 h2 h3
  done

lemma I_max (n : Nat) : n ∈ I (n + 1) := by
  define
  linarith
  done

lemma I_diff (n : Nat) : I (n + 1) \ {n} = I n := by
  apply Set.ext
  fix x : Nat
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ I (n + 1) \ {n}
    define                --Goal : x < n
    define at h1
    have h2 : x ∈ I (n + 1) := h1.left
    have h3 : ¬x ∈ {n} := h1.right
    define at h2          --h2 : x < n + 1
    define at h3          --h3 : ¬x = n
    have h4 : x ≤ n := Nat.le_of_lt_succ h2
    show x < n from Nat.lt_of_le_of_ne h4 h3
    done
  · -- (←)
    assume h1 : x ∈ I n
    define at h1          --h1 : x < n
    define                --Goal : x ∈ I (n + 1) ∧ ¬x ∈ {n}
    apply And.intro
    · -- Proof that x ∈ I (n + 1)
      define              --Goal : x < n + 1
      linarith
      done
    · -- Proof that x ∉ {n}
      by_contra h2        --h2 : x ∈ {n}
      define at h2        --h2 : x = n
      linarith
      done
    done
  done

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n := by
  have h3 : n ∈ I (n + 1) := I_max n
  rewrite [numElts_def] at h1     --h1 : I (n + 1) ∼ X
  have h4 : I (n + 1) \ {n} ∼ X \ {x} := remove_one_equinum h1 h3 h2
  rewrite [I_diff] at h4          --h4 : I n ∼ X \ {x}
  show numElts (X \ {x}) n from h4
  done
  
lemma one_match_def {A B : Type} (a x : A) (b y : B) :
    one_match a b x y ↔ x = a ∧ y = b := by rfl

lemma one_match_match {A B : Type} (a : A) (b : B) :
    matching (one_match a b) {a} {b} := sorry

lemma I_1_singleton : I 1 = {0} := by
  apply Set.ext
  fix x : Nat
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ I 1
    rewrite [I_def] at h1  --h1 : x < 1
    define                 --Goal : x = 0
    linarith
    done
  · -- (←)
    assume h1 : x ∈ {0}
    define at h1           --h1 : x = 0
    rewrite [h1, I_def]    --Goal : 0 < 1
    linarith
    done
  done

lemma singleton_of_diff_empty {A : Type} {X : Set A} {x : A}
    (h1 : x ∈ X) (h2 : empty (X \ {x})) : X = {x} := by
  apply Set.ext
  fix a : A
  apply Iff.intro
  · -- (→)
    assume h3 : a ∈ X
    contradict h2 with h4
    apply Exists.intro a
    define
    show a ∈ X ∧ ¬a ∈ {x} from And.intro h3 h4
    done
  · -- (←)
    assume h3 : a ∈ {x}
    define at h3
    rewrite [h3]
    show x ∈ X from h1
    done
  done

lemma singleton_one_elt {A : Type} (a : A) : numElts {a} 1 := by
  define
  rewrite [I_1_singleton]
  show ∃ (R : Rel Nat A), matching R {0} {a} from
    Exists.intro (one_match 0 a) (one_match_match 0 a)
  done

theorem one_elt_iff_singleton {A : Type} (X : Set A) :
    numElts X 1 ↔ ∃ (x : A), X = {x} := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts X 1  --Goal : ∃ (x : A), X = {x}
    have h2 : 1 > 0 := by norm_num
    obtain (x : A) (h3 : x ∈ X) from nonempty_of_pos_numElts h1 h2
    have h4 : numElts (X \ {x}) 0 := remove_one_numElts h1 h3
    rewrite [zero_elts_iff_empty] at h4
    show ∃ (x : A), X = {x} from
      Exists.intro x (singleton_of_diff_empty h3 h4)
    done
  · -- (←)
    assume h1 : ∃ (x : A), X = {x}
    obtain (x : A) (h2 : X = {x}) from h1
    rewrite [h2]
    show numElts {x} 1 from singleton_one_elt x
    done
  done