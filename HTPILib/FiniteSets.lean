import HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true

def empty {A : Type} (X : Set A) : Prop := ¬∃ (x : A), x ∈ X
def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
    { (b, a) : B × A | (a, b) ∈ R }
theorem Theorem_4_2_5_1 {A B : Type}
    (R : Set (A × B)) : inv (inv R) = R := by rfl
theorem simp_inv {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

/- Basic properties of finite sets -/

def I (n : Nat) : Set Nat := { k : Nat | 1 ≤ k ∧ k ≤ n }

theorem I_1 {n : Nat} (h : n > 0) : 1 ∈ I n := by
  define
  apply And.intro _ h
  norm_num
  done

theorem I_top {n : Nat} (h : n > 0) : n ∈ I n := by
  define
  apply And.intro h
  exact Nat.le_refl n
  done

theorem I_0_empty : empty (I 0) := by
  define
  by_contra h1
  obtain x h2 from h1
  define at h2
  linarith
  done

theorem I_1_singleton : I 1 = {1} := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1
    define
    exact Nat.le_antisymm h1.right h1.left
    done
  · -- (←)
    assume h1
    define at h1
    rewrite [h1]
    exact I_1 zero_lt_one
    done
  done

theorem I_diff (n : Nat) : I (n + 1) \ { n + 1 } = I n := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define
    define at h1
    have h2 := h1.left
    have h3 := h1.right
    define at h2
    define at h3
    apply And.intro h2.left
    have h4 : x < n + 1 := Nat.lt_of_le_of_ne h2.right h3
    exact Nat.le_of_lt_succ h4
    done
  · -- (←)
    assume h1
    define; define at h1
    apply And.intro
    · -- Proof that x ∈ I (n + 1)
      define
      apply And.intro h1.left
      linarith
      done
    · -- Proof that x ∉ {n + 1}
      by_contra h2
      define at h2
      rewrite [h2] at h1
      linarith
      done
    done
  done

def pairing {A B : Type} (R : Set (A × B)) (X : Set A) (Y : Set B) : Prop :=
    ∀ (x : A) (y : B), (x, y) ∈ R → x ∈ X ∧ y ∈ Y

def match_from {A B : Type} (R : Set (A × B)) (X : Set A) : Prop :=
    ∀ x ∈ X, ∃! (y : B), (x, y) ∈ R

def matching {A B : Type} (R : Set (A × B)) (X : Set A) (Y : Set B) : Prop :=
    pairing R X Y ∧ match_from R X ∧ match_from (inv R) Y

def equinum {A B : Type} (X : Set A) (Y : Set B) : Prop :=
    ∃ (R : Set (A × B)), matching R X Y

def numElts {A : Type} (X : Set A) (n : Nat) : Prop :=
    equinum (I n) X

def finite {A : Type} (X : Set A) : Prop := ∃ (n : Nat), numElts X n

def swap {A B : Type} (R : Set (A × B)) (j k : A) : Set (A × B) :=
    { (x, y) : A × B | (x = j ∧ (k, y) ∈ R) ∨ (x = k ∧ (j, y) ∈ R) ∨ (x ≠ j ∧ x ≠ k ∧ (x, y) ∈ R) }

theorem match_pair {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B} {j : A} {u : B}
    (h1 : matching R X Y) (h2 : (j, u) ∈ R) : j ∈ X ∧ u ∈ Y := by
  define at h1
  have h3 := h1.left
  define at h3
  exact h3 j u h2
  done

theorem match_inv {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B}
    (h : matching R X Y) : matching (inv R) Y X := by
  define
  apply And.intro
  · -- Proof that pairing R Y X
    define
    fix y; fix x
    assume h1
    define at h1
    have h2 := match_pair h h1
    exact And.intro h2.right h2.left
    done
  · -- proof that match_from (inv R) Y ∧ match_from (inv (inv R)) X
    rewrite [Theorem_4_2_5_1]
    define at h
    exact And.intro h.right.right h.right.left
    done
  done

theorem match_unique {A B : Type} {R : Set (A × B)} {X : Set A} {j : A} {u v : B}
    (h1 : match_from R X) (h2 : j ∈ X) (h3 : (j, u) ∈ R) (h4 : (j, v) ∈ R) : u = v := by
  define at h1
  have h5 := h1 j h2
  obtain z _h6 h7 from h5
  exact h7 u v h3 h4
  done

theorem swap_comm {A B : Type} (R : Set (A × B)) (j k : A) :
    swap R j k = swap R k j := by
  apply Set.ext
  fix (x, y)
  exact
    calc (x, y) ∈ swap R j k
        ↔ (x = j ∧ (k, y) ∈ R) ∨ ((x = k) ∧ (j, y) ∈ R) ∨ (x ≠ j ∧ x ≠ k ∧ (x, y) ∈ R) := by rfl
      _ ↔ (x = k ∧ (j, y) ∈ R) ∨ ((x = j) ∧ (k, y) ∈ R) ∨ (x ≠ k ∧ x ≠ j ∧ (x, y) ∈ R) :=
          by
            rw [←or_assoc, @or_comm (x = j ∧ (k, y) ∈ R), ←and_assoc, @and_comm (x ≠ j),
              and_assoc, or_assoc]
      _ ↔ (x, y) ∈ swap R k j := by rfl

theorem swap_iff_1 {A B : Type} (R : Set (A × B)) (j k : A) (y : B) :
    (j, y) ∈ swap R j k ↔ (k, y) ∈ R := by
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1
    by_cases on h1
    · -- Case 1.
      exact h1.right
      done
    · -- Case 2.
      by_cases on h1
      · -- Case 2.1.
        rewrite [h1.left] at h1
        exact h1.right
        done
      · -- Case 2.2.
        contradict h1.left
        rfl
        done
      done
    done
  · -- (←)
    assume h1
    define
    apply Or.inl
    apply And.intro _ h1
    rfl
    done
  done

theorem swap_iff_2 {A B : Type} (R : Set (A × B)) (j k : A) (y : B) :
    (k, y) ∈ swap R j k ↔ (j, y) ∈ R := by
  rewrite [swap_comm]
  exact swap_iff_1 R k j y

theorem swap_iff_3 {A B : Type} (R : Set (A × B)) {j k x : A} (y : B)
    (h1 : x ≠ j) (h2 : x ≠ k) : (x, y) ∈ swap R j k ↔ (x, y) ∈ R := by
  apply Iff.intro
  · -- (→)
    assume h3
    define at h3
    by_cases on h3
    · -- Case 1. h3 : x = j ∧ (k, y) ∈ R
      exact absurd h3.left h1
      done
    · -- Case 2
      by_cases on h3
      · -- Case 2.1. h3 : x = k ∧ (j, y) ∈ R
        exact absurd h3.left h2
        done
      · -- Case 2.2. h3 : x ≠ j ∧ y ≠ k ∧ (x, y) ∈ R
        exact h3.right.right
        done
      done
    done
  · -- (←)
    assume h3
    define
    exact Or.inr (Or.inr (And.intro h1 (And.intro h2 h3)))
    done
  done

theorem inv_swap_sub_swap_inv {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B} {j k : A} {u v : B}
    (h1 : matching R X Y) (h2 : (j, u) ∈ R) (h3 : (k, v) ∈ R) :
    inv (swap R j k) ⊆ swap (inv R) u v := by
  fix (y, x)
  assume h4
  define at h4
  have h5 := match_pair h1 h2
  have h6 := match_pair h1 h3
  by_cases on h4
  · -- Case 1. h4 : x = j ∧ (k, y) ∈ R
    have h7 := match_unique h1.right.left h6.left h4.right h3
    rewrite [h7, swap_iff_2, h4.left, simp_inv]
    exact h2
    done
  · -- Case 2.
    by_cases on h4
    · -- Case 2.1. h4 : x = k ∧ (j, y) ∈ R
      have h7 := match_unique h1.right.left h5.left h4.right h2
      rewrite [h7, swap_iff_1, h4.left, simp_inv]
      exact h3
      done
    · -- Case 2.2. h4 : x ≠ j ∧ x ≠ k ∧ (x, y) ∈ R
      rewrite [←simp_inv] at h2 h3 h4
      have h7 : y ≠ u := by
        contradict h4.left with h7
        rewrite [h7] at h4
        exact match_unique h1.right.right h5.right h4.right.right h2
        done
      have h8 : y ≠ v := by
        contradict h4.right.left with h8
        rewrite [h8] at h4
        exact match_unique h1.right.right h6.right h4.right.right h3
        done
      rewrite [swap_iff_3 (inv R) x h7 h8]
      exact h4.right.right
      done
    done
  done

theorem inv_swap_comm {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B} {j k : A} {u v : B}
    (h1 : matching R X Y) (h2 : (j, u) ∈ R) (h3 : (k, v) ∈ R) :
    inv (swap R j k) = swap (inv R) u v := by
  apply Set.ext
  fix (y, x)
  apply Iff.intro
  · -- (→)
    assume h4
    exact inv_swap_sub_swap_inv h1 h2 h3 h4
    done
  · -- (←)
    assume h4
    rewrite [←simp_inv] at h4
    rewrite [simp_inv, ←Theorem_4_2_5_1 R]
    exact inv_swap_sub_swap_inv (match_inv h1) h2 h3 h4
  done

theorem match_from_swap_1 {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B}
    {j k : A} {v : B} (h1 : matching R X Y) (h2 : (k, v) ∈ R) :
    j ∈ X → ∃! (y : B), (j, y) ∈ swap R j k := by
  have h3 := match_pair h1 h2
  assume h4
  exists_unique
  · -- Existence
    apply Exists.intro v
    rewrite [swap_iff_1]
    exact h2
    done
  · -- Uniqueness
    fix y1; fix y2
    assume h5; assume h6
    rewrite [swap_iff_1] at h5 h6
    define at h1
    exact match_unique h1.right.left h3.left h5 h6
    done
  done

theorem match_from_swap {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B}
    {j k : A} {u v : B} (h1 : matching R X Y) (h2 : (j, u) ∈ R) (h3 : (k, v) ∈ R) :
    match_from (swap R j k) X := by
  define
  fix x
  by_cases h4 : x = j
  · -- Case 1. h4 : x = j
    rewrite [h4]
    exact match_from_swap_1 h1 h3
    done
  · -- Case 2. h4 : x ≠ j
    by_cases h5 : x = k
    · -- Case 2.1. h5 : x = k
      rewrite [h5, swap_comm]
      exact match_from_swap_1 h1 h2
      done
    · -- Case 2.2. h5 : x ≠ k
      assume h6
      define at h1
      have h7 := h1.right.left x h6
      obtain y h8 _h9 from h7
      exists_unique
      · -- Existence
        apply Exists.intro y
        rewrite [swap_iff_3 R y h4 h5]
        exact h8
        done
      · -- Uniqueness
        fix y1; fix y2
        assume h10; assume h11
        rewrite [swap_iff_3 R y1 h4 h5] at h10
        rewrite [swap_iff_3 R y2 h4 h5] at h11
        exact match_unique h1.right.left h6 h10 h11
        done
      done
    done
  done

theorem matching_swap {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B} {j k : A} 
    (h1 : matching R X Y) (h2 : j ∈ X) (h3 : k ∈ X) : matching (swap R j k) X Y := by
  define
  define at h1
  have h4 := h1.right.left
  define at h4
  obtain u h5 _h6 from h4 j h2
  obtain v h7 _h8 from h4 k h3
  apply And.intro
  · -- Proof of pairing
    define
    fix x; fix y
    assume h9
    define at h9
    by_cases on h9
    · -- Case 1. h9 : x = j ∧ (k, y) ∈ R
      rewrite [h9.left]
      apply And.intro h2
      exact (match_pair h1 h9.right).right
      done
    · -- Case 2.
      by_cases on h9
      · -- Case 2.1. h9 : x = k ∧ (j, y) ∈ R
        rewrite [h9.left]
        apply And.intro h3
        exact (match_pair h1 h9.right).right
        done
      · -- Case 2.2. h9 : x ≠ j ∧ y ≠ k ∧ (x, y) ∈ R
        exact match_pair h1 h9.right.right
        done
      done
    done
  · -- Proof of match_froms
    apply And.intro (match_from_swap h1 h5 h7)
    have h9 := match_inv h1
    rewrite [inv_swap_comm h1 h5 h7]
    rewrite [←simp_inv] at h5 h7
    exact match_from_swap h9 h5 h7
    done
  done

theorem pair_eq {A B : Type} (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) = (a2, b2) ↔ a1 = a2 ∧ b1 = b2 := by
  apply Iff.intro
  · -- (→)
    assume h1
    apply And.intro
    · -- Proof that a1 = a2
      exact
        calc a1
            = (a1, b1).1 := by rfl
          _ = (a2, b2).1 := by rw [h1]
          _ = a2 := by rfl
      done
    · -- Proof that b1 = b2
      exact
        calc b1
            = (a1, b1).2 := by rfl
          _ = (a2, b2).2 := by rw [h1]
          _ = b2 := by rfl
      done
    done
  · -- (←)
    assume h1
    rewrite [h1.left, h1.right]
    rfl
    done
  done

theorem pair_flip {A B : Type} (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) = (a2, b2) ↔ (b1, a1) = (b2, a2) := by
  simp [pair_eq, and_comm]
  done

theorem inv_cut_sub {A B : Type} (R : Set (A × B)) (w : A) (z : B) :
    inv (R \ { (w, z) }) ⊆ (inv R) \ { (z, w) } := by
  fix (b, a)
  assume h1
  define at h1
  define
  rewrite [simp_inv]
  apply And.intro h1.left
  contradict h1.right with h2
  define; define at h2
  rewrite [pair_flip]
  exact h2
  done

theorem match_from_cut {A B : Type} {R : Set (A × B)} {X : Set A} {w : A} {z : B}
    (h1 : match_from R X) (h2 : (w, z) ∈ R) : match_from (R \ { (w, z) }) (X \ {w}) := by
  define; define at h1
  fix x
  assume h3
  define at h3
  obtain y h4 h5 from h1 x h3.left
  exists_unique
  · -- Existence
    apply Exists.intro y
    define
    apply And.intro h4
    contradict h3.right with h6
    define
    define at h6
    exact ((pair_eq x w y z).ltr h6).left
    done
  · -- Uniqueness
    fix y1; fix y2
    assume h6; assume h7
    define at h6; define at h7
    exact h5 y1 y2 h6.left h7.left
    done
  done

theorem match_from_pair {A B : Type} {R : Set (A × B)} {X : Set A} {x w : A} {y z : B}
    (h1 : match_from R X) (h2 : (x, y) ∈ R) (h3 : (w, z) ∈ R) (h4 : x = w) (h5 : x ∈ X) :
    (x, y) = (w, z) := by
  rewrite [pair_eq]
  apply And.intro h4
  rewrite [←h4] at h3
  exact match_unique h1 h5 h2 h3
  done

theorem matching_cut {A B : Type} {R : Set (A × B)} {X : Set A} {Y : Set B} {w : A} {z : B}
    (h1 : matching R X Y) (h2 : (w, z) ∈ R) :
    matching (R \ { (w, z) }) (X \ {w}) (Y \ {z}) := by
  define
  apply And.intro
  · -- Proof of pairing
    define
    fix x; fix y
    assume h3
    define at h3
    have h4 := match_pair h1 h3.left
    have h5 := h3.right
    define at h5
    apply And.intro
    · -- Proof that x ∈ X \ {w}
      apply And.intro h4.left
      define
      contradict h5 with h6
      exact match_from_pair h1.right.left h3.left h2 h6 h4.left
      done
    · -- Proof that y ∈ Y \ {z}
      apply And.intro h4.right
      define
      contradict h5 with h6
      have h7 := h3.left
      rewrite [←simp_inv] at h2 h7
      have h8 := match_from_pair h1.right.right h7 h2 h6 h4.right
      rewrite [pair_flip]
      exact h8
      done
    done
  · -- Proofs of match_from
    apply And.intro (match_from_cut h1.right.left h2)
    have h3 : inv (R \ { (w, z) }) = (inv R) \ { (z, w) } := by
      apply Set.ext
      fix (b, a)
      apply Iff.intro
      · -- (→)
        assume h3
        exact inv_cut_sub R w z h3
        done
      · -- (←)
        assume h3
        rewrite [←simp_inv] at h3 |-
        exact inv_cut_sub (inv R) z w h3
        done
      done
    rewrite [h3]
    rewrite [←simp_inv] at h2
    exact match_from_cut h1.right.right h2  
    done
  done

theorem empty_match_from {A B : Type} (R : Set (A × B)) (X : Set A) (h : empty X) : match_from R X := by
  define
  fix x
  assume h1
  define at h
  contradict h
  exact Exists.intro x h1
  done

theorem one_elt_match_from {A B : Type} (a : A) (b : B) : match_from {(a, b)} {a} := by
  define
  fix x
  assume h1
  define at h1
  rewrite [h1]
  exists_unique
  · -- Existence
    apply Exists.intro b
    define
    rfl
    done
  · -- Uniqueness
    fix b1; fix b2
    assume h2; assume h3
    define at h2; define at h3
    rewrite [←h3] at h2
    exact ((pair_eq a a b1 b2).ltr h2).right
    done
  done

/- Basic theorems about finite sets and number of elements -/

theorem remove_one_equinum {A B : Type} {X : Set A} {Y : Set B} {x : A} {y : B}
    (h1 : equinum X Y) (h2 : x ∈ X) (h3 : y ∈ Y) : equinum (X \ { x }) (Y \ { y }) := by
  define
  obtain R h4 from h1
  have h5 := h4.right.right y h3
  obtain j h6 _h7 from h5
  define at h6
  have h8 := match_pair h4 h6
  have h9 := matching_swap h4 h2 h8.left
  have h10 : (x, y) ∈ swap R x j := by
    define
    apply Or.inl
    apply And.intro _ h6
    rfl
    done
  let R' := (swap R x j) \ { (x, y) }
  have h11 := matching_cut h9 h10
  exact Exists.intro R' h11
  done

theorem remove_one_numElts {A : Type} {X : Set A} {n : Nat} {x : A}
    (h1 : numElts X (n + 1)) (h2 : x ∈ X) : numElts (X \ {x}) n := by
  have h3 : n + 1 ∈ I (n + 1) := I_top (Nat.zero_lt_succ n)
  unfold numElts at h1
  have h4 := remove_one_equinum h1 h3 h2
  rewrite [I_diff] at h4
  exact h4
  done

theorem zero_elts_iff_empty {A : Type} (X : Set A) : numElts X 0 ↔ empty X := by
  apply Iff.intro
  · -- (→)
    assume h1
    define
    by_contra h2
    obtain x h3 from h2
    define at h1
    obtain R h4 from h1
    obtain j h5 _h6 from h4.right.right x h3
    define at h5
    have h7 := match_pair h4 h5
    have h8 := h7.left
    define at h8
    linarith
    done
  · -- (←)
    assume h1
    define
    apply Exists.intro ∅
    define
    apply And.intro
    · -- Proof of pairing
      define
      fix n; fix a
      assume h2
      define at h2
      exact False.elim h2
      done
    · -- Proofs of match_from
      apply And.intro
      · -- Proof of match_from ∅ (I 0)
        exact empty_match_from _ (I 0) I_0_empty
        done
      · -- Proof of match_from (inv ∅) X
        exact empty_match_from _ X h1
        done
      done
    done
  done

theorem one_elt_iff_singleton {A : Type} (X : Set A) : numElts X 1 ↔ ∃ (x : A), X = {x} := by
  define : numElts X 1
  rewrite [I_1_singleton]
  apply Iff.intro
  · -- (→)
    assume h1
    obtain R h2 from h1
    have h3 : 1 ∈ ({1} : Set Nat) := by define; rfl
    obtain x h4 _h5 from h2.right.left 1 h3
    have h6 := match_pair h2 h4
    apply Exists.intro x
    apply Set.ext
    fix a
    apply Iff.intro
    · -- (→)
      assume h7
      define
      have h8 := h2.right.right a h7
      obtain j h9 _h10 from h8
      define at h9
      have h11 := match_pair h2 h9 
      have h12 := h11.left
      define at h12
      rewrite [h12] at h9
      exact match_unique h2.right.left h3 h9 h4
      done
    · -- (←)
      assume h7
      define at h7
      rewrite [h7]
      exact h6.right
      done
    done
  · -- (←)
    assume h1
    obtain x h2 from h1
    let R : Set (Nat × A) := {(1, x)}
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of pairing R {1} X
      define
      fix n; fix a
      assume h3
      define at h3
      rewrite [pair_eq n 1 a x] at h3
      rewrite [h3.left, h3.right, h2]
      apply And.intro
      · -- Proof that 1 ∈ {1}
        define
        rfl
        done
      · -- Proof that x ∈ {x}
        define
        rfl
        done
      done
    · -- Proof of matchings
      apply And.intro
      · -- Proof that match_from R {1}
        exact one_elt_match_from 1 x
        done
      · -- Proof that match_from (inv R) X
        have h3 : inv R = {(x, 1)} := by
          apply Set.ext
          fix (a, n)
          define : (a, n) ∈ ({(x, 1)} : Set (A × Nat))
          define : (a, n) ∈ inv R
          exact pair_flip n 1 a x
          done
        rewrite [h2, h3]
        exact one_elt_match_from x 1
        done
      done
    done
  done

theorem nonempty_of_pos_numElts {A : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (h2 : n > 0) : ∃ (x : A), x ∈ X := by
  obtain R h3 from h1
  have h4 : 1 ∈ I n := I_1 h2
  have h5 := h3.right.left 1 h4
  obtain x h6 _h7 from h5
  have h8 := match_pair h3 h6
  exact Exists.intro x h8.right