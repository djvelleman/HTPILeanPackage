/- Copyright 2023 Daniel J. Velleman -/

import HTPILib.Chap5
namespace HTPI

/- Definitions -/
def invRel {U V : Type} (R : Rel U V) : Rel V U :=
  RelFromExt (inv (extension R))

def rel_within {U V : Type} (R : Rel U V) (A : Set U) (B : Set V) : Prop :=
  ∀ ⦃x : U⦄ ⦃y : V⦄, R x y → x ∈ A ∧ y ∈ B

def fcnl_on {U V : Type} (R : Rel U V) (A : Set U) : Prop :=
  ∀ ⦃x : U⦄, x ∈ A → ∃! (y : V), R x y

def matching {U V : Type} (R : Rel U V) (A : Set U) (B : Set V) : Prop :=
  rel_within R A B ∧ fcnl_on R A ∧ fcnl_on (invRel R) B

def equinum {U V : Type} (A : Set U) (B : Set V) : Prop :=
  ∃ (R : Rel U V), matching R A B

notation:50  A:50 " ∼ " B:50 => equinum A B

def RelWithinFromFunc {U V : Type} (f : U → V) (A : Set U)
  (x : U) (y : V) : Prop := x ∈ A ∧ f x = y

def one_one_on {U V : Type} (f : U → V) (A : Set U) : Prop :=
  ∀ ⦃x1 x2 : U⦄, x1 ∈ A → x2 ∈ A → f x1 = f x2 → x1 = x2

def Univ (U : Type) : Set U := { x : U | True }

def compRel {U V W : Type} (S : Rel V W) (R : Rel U V) : Rel U W :=
  RelFromExt (comp (extension S) (extension R))

def I (n : Nat) : Set Nat := { k : Nat | k < n }

def finite {U : Type} (A : Set U) : Prop :=
  ∃ (n : Nat), I n ∼ A

def denum {U : Type} (A : Set U) : Prop :=
  Univ Nat ∼ A

def ctble {U : Type} (A : Set U) : Prop :=
  finite A ∨ denum A

def numElts {U : Type} (A : Set U) (n : Nat) : Prop := I n ∼ A

def emptyRel (U V : Type) (x : U) (y : V) : Prop := False

def remove_one {U V : Type} (R : Rel U V) (u : U) (v : V)
  (x : U) (y : V) : Prop := x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y))

def one_match {U V : Type} (a : U) (b : V)
  (x : U) (y : V) : Prop := x = a ∧ y = b

/- Section 8.1 -/
lemma invRel_def {U V : Type} (R : Rel U V) (u : U) (v : V) :
    invRel R v u ↔ R u v := by rfl

theorem equinum_image {U V : Type} {A : Set U} {B : Set V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B) : A ∼ B := by
  rewrite [←h2]
  define   --Goal : ∃ (R : Rel U V), matching R A (image f A)
  set R : Rel U V := RelWithinFromFunc f A
  apply Exists.intro R
  define   --Goal : rel_within R A (image f A) ∧
           --fcnl_on R A ∧ fcnl_on (invRel R) (image f A)
  apply And.intro
  · -- Proof of rel_within
    define --Goal : ∀ ⦃x : U⦄ ⦃y : V⦄, R x y → x ∈ A ∧ y ∈ image f A
    fix x : U; fix y : V
    assume h3 : R x y  --Goal : x ∈ A ∧ y ∈ image f A
    define at h3       --h3 : x ∈ A ∧ f x = y
    apply And.intro h3.left
    define
    show ∃ (x : U), x ∈ A ∧ f x = y from Exists.intro x h3
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R A
      define  --Goal : ∀ ⦃x : U⦄, x ∈ A → ∃! (y : V), R x y
      fix x : U
      assume h3 : x ∈ A
      exists_unique
      · -- Existence
        apply Exists.intro (f x)
        define  --Goal : x ∈ A ∧ f x = f x
        apply And.intro h3
        rfl
        done
      · -- Uniqueness
        fix y1 : V; fix y2 : V
        assume h4 : R x y1
        assume h5 : R x y2   --Goal : y1 = y2
        define at h4; define at h5
          --h4 : x ∈ A ∧ f x = y1;  h5 : x ∈ A ∧ f x = y2
        rewrite [h4.right] at h5
        show y1 = y2 from h5.right
        done
      done
    · -- Proof of fcnl_on (invRel R) (image f A)
      define  --Goal : ∀ ⦃x : V⦄, x ∈ image f A → ∃! (y : U), invRel R x y
      fix y : V
      assume h3 : y ∈ image f A
      obtain (x : U) (h4 : x ∈ A ∧ f x = y) from h3
      exists_unique
      · -- Existence
        apply Exists.intro x
        define
        show x ∈ A ∧ f x = y from h4
        done
      · -- Uniqueness
        fix x1 : U; fix x2 : U
        assume h5 : invRel R y x1
        assume h6 : invRel R y x2
        define at h5; define at h6
          --h5 : x1 ∈ A ∧ f x1 = y;  h6 : x2 ∈ A ∧ f x2 = y
        rewrite [←h6.right] at h5
        show x1 = x2 from h1 h5.left h6.left h5.right
        done
      done
    done
  done

lemma id_one_one_on {U : Type} (A : Set U) : one_one_on id A := by
  define
  fix x1 : U; fix x2 : U
  assume h1 : x1 ∈ A
  assume h2 : x2 ∈ A
  assume h3 : id x1 = id x2
  show x1 = x2 from h3
  done

lemma image_id {U : Type} (A : Set U) : image id A = A := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ image id A
    obtain (y : U) (h2 : y ∈ A ∧ id y = x) from h1
    rewrite [←h2.right]
    show id y ∈ A from h2.left
    done
  · -- (←)
    assume h1 : x ∈ A
    apply Exists.intro x  --Goal : x ∈ A ∧ id x = x
    apply And.intro h1
    rfl
    done
  done

theorem Theorem_8_1_3_1 {U : Type} (A : Set U) : A ∼ A :=
  equinum_image (id_one_one_on A) (image_id A)

lemma inv_inv {U V : Type} (R : Rel U V) : invRel (invRel R) = R := by rfl

lemma inv_match {U V : Type} {R : Rel U V} {A : Set U} {B : Set V}
    (h : matching R A B) : matching (invRel R) B A := by
  define       --Goal : rel_within (invRel R) B A ∧
               --fcnl_on (invRel R) B ∧ fcnl_on (invRel (invRel R)) A
  define at h  --h : rel_within R A B ∧ fcnl_on R A ∧ fcnl_on (invRel R) B
  apply And.intro
  · -- Proof that rel_within (invRel R) B A
    define     --Goal : ∀ ⦃x : V⦄ ⦃y : U⦄, invRel R x y → x ∈ B ∧ y ∈ A
    fix y : V; fix x : U
    assume h1 : invRel R y x
    define at h1  --h1 : R x y
    have h2 : x ∈ A ∧ y ∈ B := h.left h1
    show y ∈ B ∧ x ∈ A from And.intro h2.right h2.left
    done
  · -- proof that fcnl_on (inv R) B ∧ fcnl_on (inv (inv R)) A
    rewrite [inv_inv]
    show fcnl_on (invRel R) B ∧ fcnl_on R A from
      And.intro h.right.right h.right.left
    done
  done

theorem Theorem_8_1_3_2 {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) : B ∼ A := by
  obtain (R : Rel U V) (h1 : matching R A B) from h
  apply Exists.intro (invRel R)
  show matching (invRel R) B A from inv_match h1
  done

lemma fcnl_exists {U V : Type} {R : Rel U V} {A : Set U} {x : U}
    (h1 : fcnl_on R A) (h2 : x ∈ A) : ∃ (y : V), R x y := by
  define at h1
  obtain (y : V) (h3 : R x y)
    (h4 : ∀ (y_1 y_2 : V), R x y_1 → R x y_2 → y_1 = y_2) from h1 h2
  show ∃ (y : V), R x y from Exists.intro y h3
  done

lemma fcnl_unique {U V : Type}
    {R : Rel U V} {A : Set U} {x : U} {y1 y2 : V} (h1 : fcnl_on R A)
    (h2 : x ∈ A) (h3 : R x y1) (h4 : R x y2) : y1 = y2 := by
  define at h1
  obtain (z : V) (h5 : R x z)
    (h6 : ∀ (y_1 y_2 : V), R x y_1 → R x y_2 → y_1 = y_2) from h1 h2
  show y1 = y2 from h6 y1 y2 h3 h4
  done

lemma compRel_def {U V W : Type}
    (S : Rel V W) (R : Rel U V) (u : U) (w : W) :
    compRel S R u w ↔ ∃ (x : V), R u x ∧ S x w := by rfl

lemma inv_comp {U V W : Type} (R : Rel U V) (S : Rel V W) :
    invRel (compRel S R) = compRel (invRel R) (invRel S) := 
  calc invRel (compRel S R)
    _ = RelFromExt (inv (comp (extension S) (extension R))) := by rfl
    _ = RelFromExt (comp (inv (extension R)) (inv (extension S))) := by
          rw [Theorem_4_2_5_5]
    _ = compRel (invRel R) (invRel S) := by rfl

lemma comp_fcnl {U V W : Type} {R : Rel U V} {S : Rel V W}
    {A : Set U} {B : Set V} {C : Set W} (h1 : matching R A B)
    (h2 : matching S B C) : fcnl_on (compRel S R) A := by
  define; define at h1; define at h2
  fix a : U
  assume h3 : a ∈ A
  obtain (b : V) (h4 : R a b) from fcnl_exists h1.right.left h3
  have h5 : a ∈ A ∧ b ∈ B := h1.left h4
  obtain (c : W) (h6 : S b c) from fcnl_exists h2.right.left h5.right
  exists_unique
  · -- Existence
    apply Exists.intro c
    rewrite [compRel_def]
    show ∃ (x : V), R a x ∧ S x c from Exists.intro b (And.intro h4 h6)
    done
  · -- Uniqueness
    fix c1 : W; fix c2 : W
    assume h7 : compRel S R a c1
    assume h8 : compRel S R a c2    --Goal : c1 = c2
    rewrite [compRel_def] at h7
    rewrite [compRel_def] at h8
    obtain (b1 : V) (h9 : R a b1 ∧ S b1 c1) from h7
    obtain (b2 : V) (h10 : R a b2 ∧ S b2 c2) from h8
    have h11 : b1 = b := fcnl_unique h1.right.left h3 h9.left h4
    have h12 : b2 = b := fcnl_unique h1.right.left h3 h10.left h4
    rewrite [h11] at h9
    rewrite [h12] at h10
    show c1 = c2 from
      fcnl_unique h2.right.left h5.right h9.right h10.right
    done
  done

lemma comp_match {U V W : Type} {R : Rel U V} {S : Rel V W}
    {A : Set U} {B : Set V} {C : Set W} (h1 : matching R A B)
    (h2 : matching S B C) : matching (compRel S R) A C := by
  define
  apply And.intro
  · -- Proof of rel_within (compRel S R) A C
    define
    fix a : U; fix c : W
    assume h3 : compRel S R a c
    rewrite [compRel_def] at h3
    obtain (b : V) (h4 : R a b ∧ S b c) from h3
    have h5 : a ∈ A ∧ b ∈ B := h1.left h4.left
    have h6 : b ∈ B ∧ c ∈ C := h2.left h4.right
    show a ∈ A ∧ c ∈ C from And.intro h5.left h6.right
    done
  · -- Proof of fcnl_on statements
    apply And.intro
    · -- Proof of fcnl_on (compRel S R) A
      show fcnl_on (compRel S R) A from comp_fcnl h1 h2
      done
    · -- Proof of fcnl_on (invRel (compRel S R)) Z
      rewrite [inv_comp]
      have h3 : matching (invRel R) B A := inv_match h1
      have h4 : matching (invRel S) C B := inv_match h2
      show fcnl_on (compRel (invRel R) (invRel S)) C from comp_fcnl h4 h3
      done
    done
  done

theorem Theorem_8_1_3_3 {U V W : Type} {A : Set U} {B : Set V} {C : Set W}
    (h1 : A ∼ B) (h2 : B ∼ C) : A ∼ C := by
  obtain (R : Rel U V) (h3 : matching R A B) from h1
  obtain (S : Rel V W) (h4 : matching S B C) from h2
  apply Exists.intro (compRel S R)
  show matching (compRel S R) A C from comp_match h3 h4
  done

lemma I_def (k n : Nat) : k ∈ I n ↔ k < n := by rfl

lemma denum_def {U : Type} (A : Set U) : denum A ↔ Univ Nat ∼ A := by rfl

/- Section 8.1½ -/
lemma numElts_def {U : Type} (A : Set U) (n : Nat) :
    numElts A n ↔ I n ∼ A := by rfl

lemma finite_def {U : Type} (A : Set U) :
    finite A ↔ ∃ (n : Nat), numElts A n := by rfl

lemma fcnl_on_empty {U V : Type}
    (R : Rel U V) {A : Set U} (h1 : empty A) : fcnl_on R A := by
  define
  fix a : U
  assume h2 : a ∈ A      --Goal : ∃! (y : V), R a y
  contradict h1 with h3  --Goal : ∃ (x : U), x ∈ A
  show ∃ (x : U), x ∈ A from Exists.intro a h2
  done

lemma empty_match {U V : Type} {A : Set U} {B : Set V}
    (h1 : empty A) (h2 : empty B) : matching (emptyRel U V) A B := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a : U; fix b : V
    assume h3 : emptyRel U V a b   --Goal : a ∈ A ∧ b ∈ B
    by_contra h4                   --Goal : False
    define at h3
    show False from h3
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on emptyRel
      show fcnl_on (emptyRel U V) A from fcnl_on_empty (emptyRel U V) h1
      done
    · -- Proof of fcnl_on (invRel emptyRel)
      show fcnl_on (invRel (emptyRel U V)) B from
        fcnl_on_empty (invRel (emptyRel U V)) h2
      done
  done

lemma I_0_empty : empty (I 0) := by
  define
  by_contra h1    --h1 : ∃ (x : Nat), x ∈ I 0
  obtain (x : Nat) (h2 : x ∈ I 0) from h1
  define at h2    --h2 : x < 0
  linarith
  done

theorem zero_elts_iff_empty {U : Type} (A : Set U) :
    numElts A 0 ↔ empty A := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 0
    define
    by_contra h2         --h2 : ∃ (x : U), x ∈ A
    obtain (x : U) (h3 : x ∈ A) from h2
    define at h1
    obtain (R : Rel Nat U) (h4 : matching R (I 0) A) from h1
    define at h4
      --h4 : rel_within R (I 0) A ∧ fcnl_on R (I 0) ∧ fcnl_on (invRel R) A
    obtain (j : Nat) (h5 : invRel R x j) from
      fcnl_exists h4.right.right h3
    define at h5         --h5 : R j x
    have h6 : j ∈ I 0 ∧ x ∈ A := h4.left h5
    contradict I_0_empty --Goal : ∃ (x : Nat), x ∈ I 0
    show ∃ (x : Nat), x ∈ I 0 from Exists.intro j h6.left
    done
  · -- (←)
    assume h1 : empty A
    show ∃ (R : Rel Nat U), matching R (I 0) A from
      Exists.intro (emptyRel Nat U) (empty_match I_0_empty h1)
    done
  done

theorem nonempty_of_pos_numElts {U : Type} {A : Set U} {n : Nat}
    (h1 : numElts A n) (h2 : n > 0) : ∃ (x : U), x ∈ A := by
  define at h1
  obtain (R : Rel Nat U) (h3 : matching R (I n) A) from h1
  define at h3
  have h4 : 0 ∈ I n := h2
  obtain (x : U) (h5 : R 0 x) from fcnl_exists h3.right.left h4
  have h6 : 0 ∈ I n ∧ x ∈ A := h3.left h5
  show ∃ (x : U), x ∈ A from Exists.intro x h6.right
  done

theorem relext {U V : Type} {R S : Rel U V}
    (h : ∀ (u : U) (v : V), R u v ↔ S u v) : R = S := by
  have h2 : extension R = extension S := by
    apply Set.ext
    fix (u, v) : U × V --Goal : (u, v) ∈ extension R ↔ (u, v) ∈ extension S
    rewrite [ext_def, ext_def]  --Goal : R u v ↔ S u v
    show R u v ↔ S u v from h u v
    done
  show R = S from
    calc R
      _ = RelFromExt (extension R) := by rfl
      _ = RelFromExt (extension S) := by rw [h2]
      _ = S := by rfl
  done

lemma remove_one_def {U V : Type} (R : Rel U V) (u x : U) (v y : V) :
    remove_one R u v x y ↔
      x ≠ u ∧ y ≠ v ∧ (R x y ∨ (R x v ∧ R u y)) := by rfl

lemma remove_one_rel_within {U V : Type}
    {R : Rel U V} {A : Set U} {B : Set V} {x u : U} {y v : V}
    (h1 : matching R A B) (h2 : remove_one R u v x y) :
    x ∈ A \ {u} ∧ y ∈ B \ {v} := by
  define at h1  --h1 : rel_within R A B ∧ fcnl_on R A ∧ fcnl_on (invRel R) B
  define at h2  --h2 : x ≠ u ∧ y ≠ v ∧ (R x y ∨ R x v ∧ R u y)
  have h3 : x ∈ A ∧ y ∈ B := by
    by_cases on h2.right.right with h3
    · -- Case 1. h3 : R x y
      show x ∈ A ∧ y ∈ B from h1.left h3
      done
    · -- Case 2. h3 : R x v ∧ R u y
      have h4 : x ∈ A ∧ v ∈ B := h1.left h3.left
      have h5 : u ∈ A ∧ y ∈ B := h1.left h3.right
      show x ∈ A ∧ y ∈ B from And.intro h4.left h5.right
      done
    done
  show x ∈ A \ {u} ∧ y ∈ B \ {v} from
    And.intro (And.intro h3.left h2.left) (And.intro h3.right h2.right.left)
  done

lemma remove_one_inv {U V : Type} (R : Rel U V) (u : U) (v : V) :
    invRel (remove_one R u v) = remove_one (invRel R) v u := by
  apply relext
  fix y : V; fix x : U
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

lemma remove_one_iff {U V : Type}
    {A : Set U} {B : Set V} {R : Rel U V} (h1 : matching R A B)
    {u : U} (h2 : u ∈ A) (v : V) {x : U} (h3 : x ∈ A \ {u}) :
    ∃ (w : U), w ∈ A ∧ ∀ (y : V), remove_one R u v x y ↔ R w y := sorry

theorem remove_one_fcnl {U V : Type}
    {R : Rel U V} {A : Set U} {B : Set V} {u : U}
    (h1 : matching R A B) (h2 : u ∈ A) (v : V) :
    fcnl_on (remove_one R u v) (A \ {u}) := by
  define
  fix x : U
  assume h3 : x ∈ A \ {u}  --Goal : ∃! (y : V), remove_one R u v x y
  obtain (w : U) (h4 : w ∈ A ∧ ∀ (y : V),
    remove_one R u v x y ↔ R w y) from remove_one_iff h1 h2 v h3
  define at h1
  exists_unique
  · -- Existence
    obtain (y : V) (h5 : R w y) from fcnl_exists h1.right.left h4.left
    apply Exists.intro y
    rewrite [h4.right]
    show R w y from h5
    done
  · -- Uniqueness
    fix y1 : V; fix y2 : V
    rewrite [h4.right, h4.right]
    assume h5 : R w y1
    assume h6 : R w y2
    show y1 = y2 from fcnl_unique h1.right.left h4.left h5 h6
    done
  done

theorem remove_one_match {U V : Type}
    {R : Rel U V} {A : Set U} {B : Set V} {u : U} {v : V}
    (h1 : matching R A B) (h2 : u ∈ A) (h3 : v ∈ B) :
    matching (remove_one R u v) (A \ {u}) (B \ {v}) := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix x : U; fix y : V
    assume h4 : remove_one R u v x y
    show x ∈ A \ {u} ∧ y ∈ B \ {v} from remove_one_rel_within h1 h4
    done
  · -- Proof of fcnl_ons
    apply And.intro (remove_one_fcnl h1 h2 v)
    rewrite [remove_one_inv]
    show fcnl_on (remove_one (invRel R) v u) (B \ {v}) from
      remove_one_fcnl (inv_match h1) h3 u
  done

theorem remove_one_equinum {U V : Type}
    {A : Set U} {B : Set V} {u : U} {v : V}
    (h1 : A ∼ B) (h2 : u ∈ A) (h3 : v ∈ B) : A \ {u} ∼ B \ {v} := by
  define
  obtain (R : Rel U V) (h4 : matching R A B) from h1
  apply Exists.intro (remove_one R u v)
  show matching (remove_one R u v) (A \ {u}) (B \ {v}) from
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

theorem remove_one_numElts {U : Type} {A : Set U} {n : Nat} {a : U}
    (h1 : numElts A (n + 1)) (h2 : a ∈ A) : numElts (A \ {a}) n := by
  have h3 : n ∈ I (n + 1) := I_max n
  rewrite [numElts_def] at h1     --h1 : I (n + 1) ∼ X
  have h4 : I (n + 1) \ {n} ∼ A \ {a} := remove_one_equinum h1 h3 h2
  rewrite [I_diff] at h4          --h4 : I n ∼ A \ {a}
  show numElts (A \ {a}) n from h4
  done
  
lemma one_match_def {U V : Type} (a x : U) (b y : V) :
    one_match a b x y ↔ x = a ∧ y = b := by rfl

lemma one_match_match {U V : Type} (a : U) (b : V) :
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

lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · -- (→)
    assume h3 : x ∈ A
    contradict h2 with h4
    apply Exists.intro x
    define
    show x ∈ A ∧ ¬x ∈ {a} from And.intro h3 h4
    done
  · -- (←)
    assume h3 : x ∈ {a}
    define at h3
    rewrite [h3]
    show a ∈ A from h1
    done
  done

lemma singleton_one_elt {U : Type} (u : U) : numElts {u} 1 := by
  define
  rewrite [I_1_singleton]
  show ∃ (R : Rel Nat U), matching R {0} {u} from
    Exists.intro (one_match 0 u) (one_match_match 0 u)
  done

theorem one_elt_iff_singleton {U : Type} (A : Set U) :
    numElts A 1 ↔ ∃ (x : U), A = {x} := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 1  --Goal : ∃ (x : U), A = {x}
    have h2 : 1 > 0 := by norm_num
    obtain (x : U) (h3 : x ∈ A) from nonempty_of_pos_numElts h1 h2
    have h4 : numElts (A \ {x}) 0 := remove_one_numElts h1 h3
    rewrite [zero_elts_iff_empty] at h4
    show ∃ (x : U), A = {x} from
      Exists.intro x (singleton_of_diff_empty h3 h4)
    done
  · -- (←)
    assume h1 : ∃ (x : U), A = {x}
    obtain (x : U) (h2 : A = {x}) from h1
    rewrite [h2]
    show numElts {x} 1 from singleton_one_elt x
    done
  done