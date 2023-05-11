import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

def compRel {A B C : Type} (S : Rel B C) (R : Rel A B)
  (a : A) (c : C) : Prop := ∃ (b : B), R a b ∧ S b c

lemma inv_comp {A B C : Type} (R : Rel A B) (S : Rel B C) :
    invRel (compRel S R) = compRel (invRel R) (invRel S) := by
  apply relext
  fix c; fix a
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1; define
    obtain b h2 from h1
    apply Exists.intro b
    rewrite [invRel_def, invRel_def, and_comm]
    exact h2
    done
  · -- (←)
    assume h1
    define at h1; define
    obtain b h2 from h1
    apply Exists.intro b
    rewrite [invRel_def, invRel_def, and_comm] at h2
    exact h2
    done
  done

lemma fcnl_comp {A B C : Type} {R : Rel A B} {S : Rel B C}
    {X : Set A} {Y : Set B}
    (h1 : matching R X Y) (h2 : fcnl_on S Y) : fcnl_on (compRel S R) X := by
  define; define at h1; define at h2
  have h3 := h1.left
  have h4 := h1.right.left
  define at h3; define at h4
  fix a
  assume h5 : a ∈ X
  obtain b h6 h7 from h4 a h5
  have h8 := h3 a b h6
  obtain c h9 h10 from h2 b h8.right
  exists_unique
  · -- Existence
    apply Exists.intro c
    define
    apply Exists.intro b
    exact And.intro h6 h9
    done
  · -- Uniqueness
    fix c1; fix c2
    assume h11; assume h12
    define at h11; define at h12
    obtain b1 h13 from h11
    obtain b2 h14 from h12
    have h15 := h7 b1 b h13.left h6
    have h16 := h7 b2 b h14.left h6
    rewrite [h15] at h13
    rewrite [h16] at h14
    exact h10 c1 c2 h13.right h14.right
    done
  done

lemma match_comp {A B C : Type} {R : Rel A B} {S : Rel B C}
    {X : Set A} {Y : Set B} {Z : Set C}
    (h1 : matching R X Y) (h2 : matching S Y Z) : matching (compRel S R) X Z := by
  define; define at h1; define at h2
  apply And.intro
  · -- Proof of rel_on (compRel S R) X Z
    define
    fix a; fix c
    assume h3 : compRel S R a c
    define at h3
    obtain b h4 from h3
    have h5 := h1.left
    define at h5
    have h6 := h2.left
    define at h6
    have h7 := h5 a b h4.left
    have h8 := h6 b c h4.right
    exact And.intro h7.left h8.right
    done
  · -- Proof of fcnl_on statements
    apply And.intro
    · -- Proof of fcnl_on (compRel S R) X
      exact fcnl_comp h1 h2.right.left
      done
    · -- Proof of fcnl_on (invRel (compRel S R)) Z
      rewrite [inv_comp]
      have h3 := match_inv h1
      have h4 := match_inv h2
      define at h3
      exact fcnl_comp h4 h3.right.left
      done
    done
  done

def id_rel_on {A : Type} (X : Set A) (a b : A) : Prop := a ∈ X ∧ a = b

lemma flip_id {A : Type} {X : Set A} {a b : A}
    (h : a ∈ X ∧ a = b) : b ∈ X ∧ b = a := by
  apply And.intro _ h.right.symm
  rewrite [←h.right]
  exact h.left
  done

lemma inv_id {A : Type} (X : Set A) : invRel (id_rel_on X) = id_rel_on X := by
  apply relext
  fix a; fix b
  rewrite [invRel_def]
  define : id_rel_on X a b
  define : id_rel_on X b a
  apply Iff.intro
  · -- (→)
    assume h1
    exact flip_id h1
    done
  · -- (←)
    assume h1
    exact flip_id h1
    done
  done

lemma fcnl_id {A : Type} (X : Set A) : fcnl_on (id_rel_on X) X := by
  define
  fix a
  assume h1
  exists_unique
  · -- Existence
    apply Exists.intro a
    define
    apply And.intro h1
    rfl
    done
  · -- Uniqueness
    fix b1; fix b2
    assume h2; assume h3
    define at h2; define at h3
    rewrite [←h2.right, ←h3.right]
    rfl
    done
  done

lemma match_id {A : Type} (X : Set A) : matching (id_rel_on X) X X := by
  define
  apply And.intro
  · -- Proof of rel_on
    define
    fix a; fix b
    assume h1
    define at h1
    apply And.intro h1.left
    rewrite [←h1.right]
    exact h1.left
    done
  · -- Proof of fcnls
    apply And.intro
    · -- Proof of fcnl_on (id_rel_on X) X
      exact fcnl_id X
      done
    · -- Proof of fcnl_on (invRel (id_rel_on X)) X
      rewrite [inv_id]
      exact fcnl_id X
      done
    done
  done

theorem Theorem_8_1_3_1 {A : Type} (X : Set A) : equinum X X := by
  define
  apply Exists.intro (id_rel_on X)
  exact match_id X
  done

theorem Theorem_8_1_3_2 {A B : Type} {X : Set A} {Y : Set B}
    (h : equinum X Y) : equinum Y X := by
  define at h; define
  obtain R h1 from h
  apply Exists.intro (invRel R)
  exact match_inv h1
  done

theorem Theorem_8_1_3_3 {A B C : Type} {X : Set A} {Y : Set B} {Z : Set C}
    (h1 : equinum X Y) (h2 : equinum Y Z) : equinum X Z := by
  define at h1; define at h2; define
  obtain R h3 from h1
  obtain S h4 from h2
  apply Exists.intro (compRel S R)
  exact match_comp h3 h4
  done

/- Subsets of natural numbers -/
/- First try
def Univ (A : Type) : Set A := { x : A | True }

def enum (R : BinRel Nat) (n : Nat) (A : Set Nat) : Prop :=
  matching R (I n) A ∧ ∀ (a1 a2 b1 b2 : Nat), R a1 b1 → R a2 b2 → a1 < a2 → b1 < b2

def add_one {A B : Type} (R : Rel A B) (u : A) (v : B) (x : A) (y : B) : Prop :=
    R x y ∨ (x = u ∧ y = v)

lemma add_one_def {A B : Type} (R : Rel A B) (u : A) (v : B) (x : A) (y : B) :
    add_one R u v x y ↔ R x y ∨ (x = u ∧ y = v) := by rfl

theorem add_one_rel_on {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {x u : A} {y v : B}
    (h1 : u ∈ X) (h2 : v ∈ Y) (h3 : matching R (X \ {u}) (Y \ {v})) (h4 : add_one R u v x y) :
    x ∈ X ∧ y ∈ Y := by
  define at h4
  by_cases on h4
  · --
    have h5 := match_rel_on h3 h4
    exact And.intro h5.left.left h5.right.left
    done
  · --
    rewrite [h4.left, h4.right]
    exact And.intro h1 h2
    done
  done

theorem add_inv_comm {A B : Type} (R : Rel A B) (u : A) (v : B) :
    invRel (add_one R u v) = add_one (invRel R) v u := by
  apply relext
  fix a; fix b
  rewrite [invRel_def, add_one_def, add_one_def, invRel_def, and_comm]
  rfl
  done

theorem add_one_fcnl_on {A B : Type} {R : Rel A B} {X : Set A} {Y : Set B} {u : A} {v : B}
    (h1 : u ∈ X) (h2 : v ∈ Y) (h3 : matching R (X \ {u}) (Y \ {v})) :
    fcnl_on (add_one R u v) X := by
  define
  fix a
  assume h4
  by_cases h5 : a = u
  · --
    exists_unique
    · --
      apply Exists.intro v
      define
      apply Or.inr
      apply And.intro h5
      rfl
      done
    · --
      fix b1; fix b2
      assume h6; assume h7
      define at h6; define at h7
      have h8 : ∀ (b : B), ¬R a b := by
        fix b
        contradict h5 with h9
        have h10 := match_rel_on h3 h9
        exact h10.left.right
        done
      disj_syll h6 (h8 b1)
      disj_syll h7 (h8 b2)
      rewrite [h6.right, h7.right]
      rfl
      done
    done
  · --
    have h6 : a ∈ X \ {u} := And.intro h4 h5
    define at h3
    have h7 := h3.right.left
    define at h7
    have h8 := h7 a h6
    obtain b h9 h10 from h8
    exists_unique
    · --
      apply Exists.intro b
      define
      exact Or.inl h9
      done
    · --
      fix b1; fix b2
      assume h11; assume h12
      have h13 : ∀ (y : B), add_one R u v a y → R a y := by
        fix y
        assume h14
        define at h14
        contradict h5 with h15
        disj_syll h14 h15
        exact h14.left
        done
      have h14 := h13 b1 h11
      have h15 := h13 b2 h12
      exact h10 b1 b2 h14 h15
      done
    done
  done
  
lemma match_add_one {A B : Type} {X : Set A} {Y : Set B} {u : A} {v : B} {R' : Rel A B}
    (h1 : u ∈ X) (h2 : v ∈ Y) (h3 : matching R' (X \ {u}) (Y \ {v})) : matching (add_one R' u v) X Y := by
  define
  apply And.intro
  · --
    define
    fix a; fix b
    assume h4
    exact add_one_rel_on h1 h2 h3 h4
    done
  · --
    apply And.intro
    · --
      exact add_one_fcnl_on h1 h2 h3
      done
    · --
      rewrite [add_inv_comm]
      have h4 := match_inv h3
      exact add_one_fcnl_on h2 h1 h4
      done
    done
  done

lemma bounded_finite : ∀ (n : Nat), ∀ (A : Set Nat),
    A ⊆ (I n) → ∃ (m : Nat) (R : BinRel Nat), enum R m A := by
  by_induc
  · -- Base Case
    fix A
    assume h1
    have h2 : empty A := by
      define
      contradict I_0_empty with h3
      obtain x h4 from h3
      exact Exists.intro x (h1 h4)
      done
    apply Exists.intro 0
    apply Exists.intro (emptyRel Nat Nat)
    define
    apply And.intro (match_emptyRel I_0_empty h2)
    fix a1; fix a2; fix b1; fix b2
    assume h3
    define at h3
    exact False.elim h3
    done
  · -- Induction Step
    fix n : Nat
    assume ih
    fix A : Set Nat
    assume h1 : A ⊆ I (n + 1)
    set A' : Set Nat := A \ {n}
    have h2 : A' ⊆ I n := by
      fix a : Nat
      assume h3 : a ∈ A'
      define at h3
      rewrite [←I_diff]
      exact And.intro (h1 h3.left) h3.right
      done  
    obtain m h3 from ih A' h2
    obtain R' h4 from h3
    by_cases h5 : n ∈ A
    · -- Case 1. h5 : n ∈ A
      apply Exists.intro (m + 1)
      set R : BinRel Nat := add_one R' m n
      apply Exists.intro R
      define at h4; define
      rewrite [←I_diff] at h4
      have h6 : m ∈ I (m + 1) := by
        define
        linarith
        done
      apply And.intro (match_add_one h6 h5 h4.left)
      fix a1; fix a2; fix b1; fix b2
      assume h7; assume h8; assume h9
      define at h7; define at h8
      have h10 : a2 ≤ m := by
        by_cases on h8
        · --
          have h10 := match_rel_on h4.left h8
          rewrite [I_diff] at h10
          have h11 := h10.left
          define at h11
          linarith
          done
        · --
          linarith
          done
        done
      have h11 : ¬(a1 = m ∧ b1 = n) := by
        demorgan
        apply Or.inl
        linarith
        done
      disj_syll h7 h11
      by_cases on h8
      · --
        exact h4.right a1 a2 b1 b2 h7 h8 h9
        done
      · --
        have h12 := match_rel_on h4.left h7
        have h13 := h2 h12.right
        define at h13
        linarith
        done
      done
    · -- Case 2. h5 : n ∉ A
      have h6 : A = A' := by
        apply Set.ext
        fix a
        apply Iff.intro
        · -- (→)
          assume h6
          define
          apply And.intro h6
          define
          contradict h5 with h7
          rewrite [h7] at h6
          exact h6
          done
        · -- (←)
          assume h6
          define at h6
          exact h6.left
          done
        done
      rewrite [h6]
      apply Exists.intro m
      apply Exists.intro R'
      exact h4
      done
    done
  done
-/

--Try with n + 1 => (n ∈ X ∧ s > 0 ∧ num_elts_below X n (s - 1)) ∨ ...
--Number of elements of X that are below m is s
/- Old version
def num_elts_below (X : Set Nat) (m s : Nat) : Prop :=
  match m with
    | 0 => s = 0
    | n + 1 => (n ∈ X ∧ ∃ (t : Nat), num_elts_below X n t ∧ s = t + 1) ∨
                (n ∉ X ∧ num_elts_below X n s)

lemma neb_base (X : Set Nat) : num_elts_below X 0 s ↔ s = 0 := by rfl

lemma neb_step (X : Set Nat) {n s : Nat} : num_elts_below X (n + 1) s ↔
    (n ∈ X ∧ ∃ (t : Nat), num_elts_below X n t ∧ s = t + 1) ∨ (n ∉ X ∧ num_elts_below X n s) := by rfl

lemma neb_step_elt {X : Set Nat} {n : Nat} (h1 : n ∈ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ ∃ (t : Nat), num_elts_below X n t ∧ s = t + 1 := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h3
    by_cases on h3
    · --
      exact h3.right
      done
    · --
      exact absurd h1 h3.left
      done
    done
  · -- (←)
    assume h2
    apply Or.inl
    exact And.intro h1 h2
    done
  done

lemma neb_step_not_elt {X : Set Nat} {n : Nat} (h1 : n ∉ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ num_elts_below X n s := by
  rewrite [neb_step]
  apply Iff.intro
  · --
    assume h2
    by_cases on h2
    · --
      exact absurd h2.left h1
      done
    · --
      exact h2.right
      done
    done
  · --
    assume h2
    apply Or.inr
    exact And.intro h1 h2
    done
  done

lemma neb_exists (X : Set Nat) : ∀ (n : Nat), ∃ (s : Nat), num_elts_below X n s := by
  by_induc
  · -- Base Case
    apply Exists.intro 0
    define
    rfl
    done
  · -- Induction Step
    fix n
    assume ih
    obtain t h1 from ih
    by_cases h2 : n ∈ X
    · -- Case 1. h2 : n ∈ X
      apply Exists.intro (t + 1)
      rewrite [neb_step_elt h2]
      apply Exists.intro t
      apply And.intro h1
      rfl
      done
    · -- Case 2. h2 : n ∉ X
      apply Exists.intro t
      rewrite [neb_step_not_elt h2]
      exact h1
      done
    done
  done

lemma neb_unique (X : Set Nat) : ∀ (n : Nat), ∀ (s1 s2 : Nat),
    num_elts_below X n s1 → num_elts_below X n s2 → s1 = s2 := by
  by_induc
  · -- Base Case
    fix s1; fix s2
    assume h1; assume h2
    define at h1; define at h2
    rewrite [h1, h2]
    rfl
  · -- Induction Step
    fix n
    assume ih
    fix s1; fix s2
    assume h1; assume h2
    by_cases h3 : n ∈ X
    · -- Case 1. h3 : n ∈ X
      rewrite [neb_step_elt h3] at h1
      rewrite [neb_step_elt h3] at h2
      obtain t1 h4 from h1
      obtain t2 h5 from h2
      have h6 := ih t1 t2 h4.left h5.left
      rewrite [h4.right, h5.right, h6]
      rfl
      done
    · -- Case 2. h3 : n ∉ X
      rewrite [neb_step_not_elt h3] at h1
      rewrite [neb_step_not_elt h3] at h2
      exact ih s1 s2 h1 h2
      done
    done
  done

/-
--Maybe break this up into existence and uniqueness parts?
lemma neb_fcnl (X : Set Nat) : ∀ (n : Nat), ∃! (m : Nat), num_elts_below X n m := by
  by_induc
  · --
    define
    apply Exists.intro 0
    apply And.intro
    define
    rfl
    fix m
    assume h
    define at h
    exact h
    done
  · --
    fix n
    assume ih
    define at ih
    obtain m h1 from ih
    define
    by_cases h2 : n ∈ X
    · --
      apply Exists.intro (m + 1)
      apply And.intro
      rewrite [neb_step_elt h2]
      apply Exists.intro m
      apply And.intro h1.left
      rfl
      fix m1
      assume h3
      rewrite [neb_step_elt h2] at h3
      obtain j h4 from h3
      have h5 := h1.right j h4.left
      rewrite [h5] at h4
      exact h4.right
      done
    · --
      apply Exists.intro m
      apply And.intro
      rewrite [neb_step_not_elt h2]
      exact h1.left
      fix m1
      assume h3
      rewrite [neb_step_not_elt h2] at h3
      exact h1.right m1 h3
      done
    done
  done
-/

def enum (X : Set Nat) (s n : Nat) : Prop := n ∈ X ∧ num_elts_below X n s

lemma neb_increase_ex {X : Set Nat} {n s : Nat} (h1 : enum X s n) :
    ∀ (m : Nat), m ≥ n + 1 → ∃ (t : Nat), num_elts_below X m t ∧ s < t := by
  by_induc
  · -- Base Case
    apply Exists.intro (s + 1)
    apply And.intro
    · -- Proof of num_elts_below X (n + 1) (s + 1)
      define at h1
      rewrite [neb_step_elt h1.left]
      apply Exists.intro s
      apply And.intro h1.right
      rfl
      done
    · -- Proof that s < s + 1
      linarith
      done
    done
  · -- Induction Step
    fix m
    assume h2
    assume ih
    obtain t h3 from ih
    by_cases h4 : m ∈ X
    · -- Case 1. h4 : m ∈ X
      apply Exists.intro (t + 1)
      rewrite [neb_step_elt h4]
      apply And.intro
      · -- Proof of ∃ (t_1 : Nat), num_elts_below X m t_1 ∧ t + 1 = t_1 + 1
        apply Exists.intro t
        apply And.intro h3.left
        rfl
        done
      · -- Proof of s < t + 1
        linarith
        done
      done
    · -- Case 2. h4 : m ∉ X
      apply Exists.intro t
      rewrite [neb_step_not_elt h4]
      exact h3
      done
    done
  done

lemma neb_increase_all {X : Set Nat} {n s : Nat} (h1 : enum X s n) :
    ∀ (m : Nat), m ≥ n + 1 → ∀ (t : Nat), num_elts_below X m t → s < t := by
  fix m
  assume h2
  obtain t h3 from neb_increase_ex h1 m h2
  fix t'
  assume h4
  have h5 := neb_unique X m t t' h3.left h4
  rewrite [h5] at h3
  exact h3.right
  done

lemma enum_not_skip {X : Set Nat} : ∀ (n s : Nat), num_elts_below X n s →
    ∀ t < s, ∃ (m : Nat), enum X t m := by
  by_induc
  · -- Base Case
    fix s
    assume h1
    rewrite [neb_base] at h1
    fix t
    contrapos
    assume h2
    linarith
    done
  · -- Induction Step
    fix n
    assume ih
    fix s
    assume h1
    by_cases h2 : n ∈ X
    · -- Case 1. h2 : n ∈ X
      rewrite [neb_step_elt h2] at h1
      obtain t' h3 from h1
      have h4 := ih t' h3.left
      fix t
      assume h5
      by_cases h6 : t = t'
      · -- Case 1.1. h6 : t = t'
        apply Exists.intro n
        define
        apply And.intro h2
        rewrite [h6]
        exact h3.left
        done
      · -- Case 1.2. h6 : t ≠ t'
        rewrite [h3.right] at h5
        have h7 : t ≤ t' := Nat.le_of_lt_succ h5
        have h8 : t < t' := Nat.lt_of_le_of_ne h7 h6
        exact h4 t h8
        done
      done
    · -- Case 2. h2 : n ∉ X
      rewrite [neb_step_not_elt h2] at h1
      exact ih s h1
      done
    done
  done

lemma bdd_subset_nat {X : Set Nat} {n s : Nat} (h1 : n ∈ X)
    (h2 : ∀ (k : Nat), k ∈ X → k ≤ n) (h3 : num_elts_below X (n + 1) s) :
    equinum (I s) X := by
  define
  apply Exists.intro (enum X)
  define
  apply And.intro
  · -- Proof of rel_on
    define
    fix t; fix m
    assume h4
    have h5 := neb_increase_ex h4
    define at h4
    apply And.intro _ h4.left
    have h6 := h2 m h4.left
    have h7 : n + 1 ≥ m + 1 := by linarith
    obtain s' h8 from h5 (n + 1) h7
    have h9 := neb_unique X (n + 1) s s' h3 h8.left
    rewrite [h9]
    define
    exact h8.right
    done
  · -- Proof of fcn_ons
    apply And.intro
    · -- proof of fcnl_on (enum X)
      define
      fix t
      assume h4
      define at h4
      have h5 := enum_not_skip (n + 1) s h3 t h4
      exists_unique
      · -- Existence
        exact h5
        done
      · -- Uniqueness
        fix m1; fix m2
        assume h6; assume h7
        have h8 : ¬m1 < m2 := by
          by_contra h9
          have h10 : m2 ≥ m1 + 1 := h9
          have h11 := neb_increase_all h6 m2 h10
          define at h7
          have h12 := h11 t h7.right
          linarith
          done
        have h9 : ¬m2 < m1 := by
          by_contra h9
          have h10 : m1 ≥ m2 + 1 := h9
          have h11 := neb_increase_all h7 m1 h10
          define at h6
          have h12 := h11 t h6.right
          linarith
          done
        linarith
        done
      done
    · -- Proof of fcnl_on (invRel (enum X))
      define
      fix m
      assume h4
      have h5 := neb_exists X m
      obtain t h6 from h5
      exists_unique
      · -- Existence
        apply Exists.intro t
        define
        exact And.intro h4 h6
        done
      · -- Uniqueness
        fix t1; fix t2
        assume h8; assume h9
        define at h8; define at h9
        exact neb_unique X m t1 t2 h8.right h9.right
        done
      done
    done
  done
-/


def num_elts_below (X : Set Nat) (m s : Nat) : Prop :=
  match m with
    | 0 => s = 0
    | n + 1 => (n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)) ∨
                (n ∉ X ∧ num_elts_below X n s)

lemma neb_step (X : Set Nat) {n s : Nat} : num_elts_below X (n + 1) s ↔
    (n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)) ∨ (n ∉ X ∧ num_elts_below X n s) := by rfl

lemma neb_step_elt {X : Set Nat} {n : Nat} (h1 : n ∈ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ 1 ≤ s ∧ num_elts_below X n (s - 1) := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h3
    by_cases on h3
    · -- Case 1. h3 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)
      exact h3.right
      done
    · -- Case 2. h3 : ¬n ∈ X ∧ num_elts_below X n s
      exact absurd h1 h3.left
      done
    done
  · -- (←)
    assume h2
    apply Or.inl
    exact And.intro h1 h2
    done
  done

lemma neb_step_not_elt {X : Set Nat} {n : Nat} (h1 : n ∉ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ num_elts_below X n s := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h2
    by_cases on h2
    · -- Case 1. h2 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)
      exact absurd h2.left h1
      done
    · -- Case 2. h2 : ¬n ∈ X ∧ num_elts_below X n s
      exact h2.right
      done
    done
  · -- (←)
    assume h2
    apply Or.inr
    exact And.intro h1 h2
    done
  done

lemma neb_exists (X : Set Nat) : ∀ (n : Nat), ∃ (s : Nat), num_elts_below X n s := by
  by_induc
  · -- Base Case
    apply Exists.intro 0
    define
    rfl
    done
  · -- Induction Step
    fix n
    assume ih
    obtain t h1 from ih
    by_cases h2 : n ∈ X
    · -- Case 1. h2 : n ∈ X
      apply Exists.intro (t + 1)
      rewrite [neb_step_elt h2, Nat.add_sub_cancel]
      apply And.intro _ h1
      linarith
      done
    · -- Case 2. h2 : n ∉ X
      apply Exists.intro t
      rewrite [neb_step_not_elt h2]
      exact h1
      done
    done
  done

lemma neb_unique (X : Set Nat) : ∀ (n : Nat), ∀ (s1 s2 : Nat),
    num_elts_below X n s1 → num_elts_below X n s2 → s1 = s2 := by
  by_induc
  · -- Base Case
    fix s1; fix s2
    assume h1; assume h2
    define at h1; define at h2
    rewrite [h1, h2]
    rfl
  · -- Induction Step
    fix n
    assume ih
    fix s1; fix s2
    assume h1; assume h2
    by_cases h3 : n ∈ X
    · -- Case 1. h3 : n ∈ X
      rewrite [neb_step_elt h3] at h1
      rewrite [neb_step_elt h3] at h2
      have h4 := ih (s1 - 1) (s2 - 1) h1.right h2.right
      show s1 = s2 from
        calc s1
          _ = s1 - 1 + 1 := (Nat.sub_add_cancel h1.left).symm
          _ = s2 - 1 + 1 := by rw [h4]
          _ = s2 := Nat.sub_add_cancel h2.left
      done
    · -- Case 2. h3 : n ∉ X
      rewrite [neb_step_not_elt h3] at h1
      rewrite [neb_step_not_elt h3] at h2
      exact ih s1 s2 h1 h2
      done
    done
  done

/-
--Maybe break this up into existence and uniqueness parts?
lemma neb_fcnl (X : Set Nat) : ∀ (n : Nat), ∃! (m : Nat), num_elts_below X n m := by
  by_induc
  · --
    define
    apply Exists.intro 0
    apply And.intro
    define
    rfl
    fix m
    assume h
    define at h
    exact h
    done
  · --
    fix n
    assume ih
    define at ih
    obtain m h1 from ih
    define
    by_cases h2 : n ∈ X
    · --
      apply Exists.intro (m + 1)
      apply And.intro
      rewrite [neb_step_elt h2]
      apply Exists.intro m
      apply And.intro h1.left
      rfl
      fix m1
      assume h3
      rewrite [neb_step_elt h2] at h3
      obtain j h4 from h3
      have h5 := h1.right j h4.left
      rewrite [h5] at h4
      exact h4.right
      done
    · --
      apply Exists.intro m
      apply And.intro
      rewrite [neb_step_not_elt h2]
      exact h1.left
      fix m1
      assume h3
      rewrite [neb_step_not_elt h2] at h3
      exact h1.right m1 h3
      done
    done
  done
-/

def enum (X : Set Nat) (s n : Nat) : Prop := n ∈ X ∧ num_elts_below X n s

lemma neb_increase {X : Set Nat} {n s : Nat} (h1 : enum X s n) :
    ∀ (m : Nat), m ≥ n + 1 → ∀ (t : Nat), num_elts_below X m t → s < t := by
  by_induc
  · -- Base Case
    define at h1
    fix t
    assume h2
    rewrite [neb_step_elt h1.left] at h2
    have h3 := neb_unique X n s (t - 1) h1.right h2.right
    show s < t from
      calc s
        _ = t - 1 := h3
        _ < t - 1 + 1 := by linarith
        _ = t := Nat.sub_add_cancel h2.left
    done
  · -- Induction Step
    fix m
    assume h2
    assume ih
    fix t
    assume h3
    by_cases h4 : m ∈ X
    · -- Case 1. h4 : m ∈ X
      rewrite [neb_step_elt h4] at h3
      have h5 := ih (t - 1) h3.right
      show s < t from
        calc s
          _ < t - 1 := h5
          _ ≤ t := Nat.sub_le _ _
      done
    · -- Case 2. h4 : m ∉ X
      rewrite [neb_step_not_elt h4] at h3
      exact ih t h3
      done
    done
  done

lemma enum_not_skip {X : Set Nat} : ∀ (m s : Nat), num_elts_below X m s →
    ∀ t < s, ∃ (n : Nat), enum X t n := by
  by_induc
  · -- Base Case
    fix s
    assume h1
    define at h1
    fix t
    contrapos
    assume h2
    linarith
    done
  · -- Induction Step
    fix m
    assume ih
    fix s
    assume h1
    by_cases h2 : m ∈ X
    · -- Case 1. h2 : m ∈ X
      rewrite [neb_step_elt h2] at h1
      have h3 := ih (s - 1) h1.right
      fix t
      assume h4
      by_cases h5 : t = s - 1
      · -- Case 1.1. h5 : t = s - 1
        apply Exists.intro m
        define
        apply And.intro h2
        rewrite [h5]
        exact h1.right
        done
      · -- Case 1.2. h5 : t ≠ s - 1
        have h6 : t ≤ s - 1 := Nat.le_pred_of_lt h4
        have h7 : t < s - 1 := Nat.lt_of_le_of_ne h6 h5
        exact ih (s - 1) h1.right t h7
        done
      done
    · -- Case 2. h2 : m ∉ X
      rewrite [neb_step_not_elt h2] at h1
      exact ih s h1
      done
    done
  done

lemma enum_not_lt {X : Set Nat} {t n1 n2 : Nat} (h1 : enum X t n1) (h2 : enum X t n2) : ¬n1 < n2 := by
  by_contra h3
  define at h2
  have h4 : n2 ≥ n1 + 1 := by linarith
  have h5 := neb_increase h1 n2 h4 t h2.right
  linarith
  done

lemma enum_unique (X : Set Nat) (t : Nat) : ∀ (n1 n2 : Nat), enum X t n1 → enum X t n2 → n1 = n2 := by
  fix n1; fix n2
  assume h1; assume h2
  have h3 : ¬n1 < n2 := enum_not_lt h1 h2
  have h4 : ¬n2 < n1 := enum_not_lt h2 h1
  linarith
  done

lemma inv_enum_fcnl (X : Set Nat) : fcnl_on (invRel (enum X)) X := by
  define
  fix n
  assume h1
  exists_unique
  · -- Existence
    obtain s h2 from neb_exists X n
    apply Exists.intro s
    define
    exact And.intro h1 h2
    done
  · -- Uniqueness
    fix s1; fix s2
    assume h2; assume h3
    define at h2; define at h3
    exact neb_unique X n s1 s2 h2.right h3.right
    done
  done

lemma bdd_subset_nat {X : Set Nat} {m s : Nat} (h1 : ∀ (n : Nat), n ∈ X → n < m)
    (h2 : num_elts_below X m s) : equinum (I s) X := by
  define
  apply Exists.intro (enum X)
  define
  apply And.intro
  · -- Proof of rel_on
    define
    fix t; fix n
    assume h3
    have h4 := neb_increase h3
    define at h3
    apply And.intro _ h3.left
    define
    have h5 := h1 n h3.left
    have h6 : m ≥ n + 1 := by linarith
    exact h4 m h6 s h2
    done
  · -- Proof of fcn_ons
    apply And.intro
    · -- proof of fcnl_on (enum X)
      define
      fix t
      assume h3
      define at h3
      exists_unique
      · -- Existence
        exact enum_not_skip m s h2 t h3
        done
      · -- Uniqueness
        exact enum_unique X t
        done
      done
    · -- Proof of fcnl_on (invRel (enum X))
      exact inv_enum_fcnl X
      done
    done
  done

def Univ (A : Type) : Set A := { x : A | True }

lemma enum_fcnl_of_unbdd {X : Set Nat} (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ n ≥ m) :
    fcnl_on (enum X) (Univ Nat) := by
  define
  by_induc
  · -- Base Case
    assume h2
    exists_unique
    · -- Existence
      obtain n h3 from h1 0
      obtain s h4 from neb_exists X (n + 1)
      have h5 := enum_not_skip (n + 1) s h4
      rewrite [neb_step_elt h3.left] at h4
      exact h5 0 h4.left
      done
    · -- Uniqueness
      exact enum_unique X 0
      done
    done
  · -- Induction Step
    fix s
    assume ih
    assume h2
    exists_unique
    · -- Existence
      have h3 : s ∈ Univ Nat := by define; trivial
      obtain m h4 h5 from ih h3
      obtain n h6 from h1 (m + 1)
      obtain t h7 from neb_exists X n
      have h8 := neb_increase h4 n h6.right t h7
      have h9 : s + 1 < t ∨ s + 1 = t := Nat.lt_or_eq_of_le h8
      by_cases on h9
      · -- Case 1. h9 : s + 1 < t
        exact enum_not_skip n t h7 (s + 1) h9
        done
      · -- Case 2. h9 : s + 1 = t
        rewrite [h9]
        apply Exists.intro n
        define
        exact And.intro h6.left h7
        done
      done
    · -- Uniqueness
      exact enum_unique X (s + 1)
      done
    done
  done

lemma unbdd_subset_nat {X : Set Nat} (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ n ≥ m) :
    equinum (Univ Nat) X := by
  define
  apply Exists.intro (enum X)
  define
  apply And.intro
  · -- Proof of rel_on
    define
    fix s; fix n
    assume h2
    define at h2
    apply And.intro _ h2.left
    define
    trivial
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on (enum X)
      exact enum_fcnl_of_unbdd h1
      done
    · -- Proof of fcnl_on (invRel (enum X))
      exact inv_enum_fcnl X
      done
    done
  done
  
/-
noncomputable def num_elts_below (X : Set Nat) (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | k + 1 => 
              have : Decidable (k ∈ X) := Classical.propDecidable (k ∈ X)
              if k ∈ X then num_elts_below X k + 1 else num_elts_below X k


def equinum2 {A B : Type} (X : Set A) (Y : Set B) : Prop :=
  ∃ (f : {a : A // a ∈ X} → {b : B // b ∈ Y}), one_to_one f ∧ onto f

theorem remove_one_equinum2 {X : Set Nat} {Y : Set Nat} {x y : Nat}
    (h1 : equinum2 X Y) (h2 : x ∈ X) (h3 : y ∈ Y) : equinum2 (X \ { x }) (Y \ { y }) := by
  define at h1
  obtain f h4 from h1
  set xx : {a : Nat // a ∈ X} := ⟨x, h2⟩
  set yy : {b : Nat // b ∈ Y} := ⟨y, h3⟩
  obtain uu h5 from h4.right yy
  set f' : {a : Nat // a ∈ X \ {x}} → {b : Nat // b ∈ Y \ {y}} :=
    fun a => if a.val = uu.val then f a else f a
  done
-/