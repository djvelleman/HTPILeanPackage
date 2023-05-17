import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Subsets of Nat are finite or denum. -/
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

lemma enum_unique (X : Set Nat) (t : Nat) :
    ∀ (n1 n2 : Nat), enum X t n1 → enum X t n2 → n1 = n2 := by
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
      have h3 : s ∈ Univ Nat := elt_Univ s
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
    denum X := by
  define
  apply Exists.intro (enum X)
  define
  apply And.intro
  · -- Proof of rel_on
    define
    fix s; fix n
    assume h2
    define at h2
    apply And.intro (elt_Univ s) h2.left
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

theorem subset_nat_ctble (X : Set Nat) : ctble X := by
  define
  by_cases h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ X → n < m
  · -- Case 1. h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ X → n < m
    apply Or.inl
    define
    obtain m h2 from h1
    obtain s h3 from neb_exists X m
    apply Exists.intro s
    exact bdd_subset_nat h2 h3
    done
  · -- Case 2. h1 : ¬∃ (m : ℕ), ∀ (n : ℕ), n ∈ X → n < m
    apply Or.inr
    push_neg at h1   --Need to explain this tactic?
    exact unbdd_subset_nat h1
    /-
    have h2 :  ∀ (m : ℕ), ∃ (n : ℕ), n ∈ X ∧ n ≥ m := by
      push_neg at h1
      fix m
      quant_neg at h1
      have h2 := h1 m
      quant_neg at h2
      obtain n h3 from h2
      conditional at h3
      apply Exists.intro n
      apply And.intro h3.left
      linarith
      done
    exact unbdd_subset_nat h2
    -/
    done
  done

/- Do equivalences for countable here -/
def unique_val_on_N {A : Type} (R : Rel Nat A) : Prop :=
  ∀ (n : Nat) (x1 x2 : A), R n x1 → R n x2 → x1 = x2

def nat_rel_onto {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  ∀ (x : A), x ∈ X → ∃ (n : Nat), R n x

lemma Lemma_8_1_5_12 {A : Type} {I : Set Nat} {X : Set A}
    (h1 : equinum I X) : ∃ (R : Rel Nat A), unique_val_on_N R ∧ nat_rel_onto R X := by
  define at h1
  obtain R h2 from h1
  define at h2
  apply Exists.intro R
  apply And.intro
  · -- Proof of unique_val_on_N
    define
    fix n; fix x1; fix x2
    assume h3; assume h4
    have h5 := h2.left
    have h6 := h2.right.left
    define at h5; define at h6
    have h7 := h5 n x1 h3
    obtain x h8 h9 from h6 n h7.left
    exact h9 x1 x2 h3 h4
    done
  · -- Proof of nat_rel_onto
    define
    fix x
    assume h3
    have h4 := h2.right.right
    define at h4
    obtain n h5 h6 from h4 x h3
    define at h5
    exact Exists.intro n h5
    done
  done

theorem Theorem_8_1_5_1_to_2 {A : Type} {X : Set A} (h1 : ctble X) :
    ∃ (R : Rel Nat A), unique_val_on_N R ∧ nat_rel_onto R X := by
  define at h1
  by_cases on h1
  · -- Case 1. h1 : finite X
    define at h1
    obtain s h2 from h1
    exact Lemma_8_1_5_12 h2
    done
  · -- Case 2. h1 : denum X
    rewrite [denum_def] at h1
    exact Lemma_8_1_5_12 h1
    done
  done

/- Old version
def fcnl_on_nat_onto {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  (∀ (n : Nat), ∃! (x : A), x ∈ X ∧ R n x) ∧ ∀ (x : A), x ∈ X → ∃ (n : Nat), R n x 
  --rel_on R (Univ Nat) X ∧ fcnl_on R (Univ Nat) ∧ ∀ x ∈ X, ∃ (n : Nat), R n x

def extend_const {A : Type} (S : Rel Nat A) (s : Nat) (a : A)
  (n : Nat) (x : A) : Prop := S n x ∨ (s ≤ n ∧ x = a)

lemma extend_const_below {A : Type} (S : Rel Nat A) {s : Nat} (a : A) (h : n < s) :
    ∀ (x : A), extend_const S s a n x ↔ S n x := by
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1
    by_cases on h1
    · -- Case 1. h1 : S n x
      exact h1
      done
    · -- Case 2. h1 : s ≤ n ∧ x = a
      contradict h1.left with h2
      linarith
      done
    done
  · -- (←)
    assume h1
    define
    exact Or.inl h1
    done
  done

lemma extend_const_above {A : Type} {S : Rel Nat A} {X : Set A} {s : Nat}
    (a : A) (h1 : rel_on S (I s) X) (h2 : s ≤ n) :
    ∀ (x : A), extend_const S s a n x ↔ x = a := by
  fix x
  apply Iff.intro
  · -- (→)
    assume h3
    define at h3
    define at h1
    by_cases on h3
    · -- Case 1. h3 : S n x
      contradict (h1 n x h3).left with h4
      define
      linarith
      done
    · -- Case 2. h3 : s ≤ n ∧ x = a
      exact h3.right
      done
    done
  · -- (←)
    assume h3
    define
    apply Or.inr
    exact And.intro h2 h3
    done
  done

theorem Theorem_8_1_5_1_to_2 {A : Type} {X : Set A} (h1 : ctble X) :
    empty X ∨ ∃ (R : Rel Nat A), fcnl_on_nat_onto R X := by
  define at h1
  by_cases on h1
  · -- h1 : finite X
    define at h1
    obtain s h2 from h1
    define at h2
    obtain S h3 from h2
    define at h3
    have h4 := h3.left
    define at h4
    or_right with h5
    obtain a h6 from h5
    set R : Rel Nat A := extend_const S s a
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof that ∀ (n : Nat), ∃! (x : A), x ∈ X ∧ R n x
      fix n : Nat
      by_cases h7 : n ∈ I s
      · -- Case 1. h7 : n ∈ I s
        have h8 := h3.right.left
        define at h8
        obtain x h9 h10 from h8 n h7
        define at h7
        have h11 : ∀ (x : A), R n x ↔ S n x := extend_const_below S a h7
        exists_unique
        · -- Existence
          apply Exists.intro x
          have h12 := h4 n x h9
          apply And.intro h12.right
          rewrite [h11]
          exact h9
          done
        · -- Uniqueness
          fix x1; fix x2
          assume h12; assume h13
          rewrite [h11] at h12
          rewrite [h11] at h13
          exact h10 x1 x2 h12.right h13.right
          done
        done
      · -- Case 2. h7 : ¬n ∈ I s
        define at h7
        have h8 : s ≤ n := by linarith
        have h9 : ∀ (x : A), R n x ↔ x = a := extend_const_above a h4 h8
        exists_unique
        · -- Existence
          apply Exists.intro a
          apply And.intro h6
          rewrite [h9]
          rfl
          done
        · -- Uniqueness
          fix x1; fix x2
          assume h10; assume h11
          rewrite [h9] at h10
          rewrite [h9] at h11
          rewrite [h10.right, h11.right]
          rfl
          done
        done
      done
    · -- Proof that ∀ (x : A), x ∈ X → ∃ (n : Nat), R n x
      fix x
      assume h7
      have h8 := h3.right.right
      define at h8
      obtain t h9 h10 from h8 x h7
      define at h9
      apply Exists.intro t
      define
      exact Or.inl h9
      done
    done
  · -- Case 2. h1 : denum X
    apply Or.inr
    define at h1
    obtain R h2 from h1
    define at h2
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof that ∀ (n : Nat), ∃! (x : A), x ∈ X ∧ R n x
      fix n
      have h3 := h2.right.left
      define at h3
      have h4 : n ∈ Univ Nat := elt_Univ n
      have h5 := h3 n h4
      obtain x h6 h7 from h5
      exists_unique
      · -- Existence
        apply Exists.intro x
        apply And.intro _ h6
        have h8 := h2.left
        define at h8
        exact (h8 n x h6).right
        done
      · -- Uniqueness
        fix x1; fix x2
        assume h8; assume h9
        exact h7 x1 x2 h8.right h9.right
        done
      done
    · -- Proof that ∀ (x : A), x ∈ X → ∃ (n : Nat), R n x
      fix x
      assume h3
      have h4 := h2.right.right
      define at h4
      obtain n h5 h6 from h4 x h3
      define at h5
      exact Exists.intro n h5
      done
    done
  done
-/

def fcnl_one_one_to_nat {A : Type} (R : Rel A Nat) (X : Set A) : Prop :=
  fcnl_on R X ∧ ∀ (x1 x2 : A) (n : Nat), x1 ∈ X → x2 ∈ X → R x1 n → R x2 n → x1 = x2

def least_witness {A : Type} (S : Rel A Nat) (x : A) (n : Nat) : Prop :=
  S x n ∧ ∀ (m : Nat), S x m → n ≤ m

theorem Theorem_8_1_5_2_to_3 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel Nat A), unique_val_on_N R ∧ nat_rel_onto R X) :
    ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  obtain S h2 from h1
  set R : Rel A Nat := least_witness (invRel S)
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of fcnl on R X
    define
    fix x
    assume h3
    exists_unique
    · -- Existence
      have h4 := h2.right
      define at h4
      obtain p h5 from h4 x h3
      set W : Set Nat := { n : Nat | S n x }
      have h6 : ∃ (n : Nat), n ∈ W := by
        apply Exists.intro p
        define
        exact h5
        done
      obtain n h7 from well_ord_princ W h6
      apply Exists.intro n
      define
      exact h7
      done
    · -- Uniqueness
      fix n1; fix n2
      assume h4; assume h5
      define at h4; define at h5
      have h6 := h4.right n2 h5.left
      have h7 := h5.right n1 h4.left
      linarith
      done
    done
  · -- Proof of one_one
    fix x1; fix x2; fix n
    assume h3; assume h4; assume h5; assume h6
    define at h5; define at h6
    have h7 := h2.left
    define at h7
    exact h7 n x1 x2 h5.left h6.left
    done
  done

/- Old version
theorem Theorem_8_1_5_2_to_3 {A : Type} {X : Set A}
    (h1 : empty X ∨ ∃ (R : Rel Nat A), fcnl_on_nat_onto R X) :
    ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  by_cases on h1
  · -- Case 1. h1 : empty X
    apply Exists.intro (emptyRel A Nat)
    define
    apply And.intro
    · --
      define
      fix x
      contrapos
      assume h2
      contradict h1 with h3
      exact Exists.intro x h3
      done
    · --
      fix x1; fix x2; fix n
      contrapos
      assume h2
      contradict h1 with h3
      exact Exists.intro x1 h3
    done
  · -- Case 2. h1 : ∃ (R : Rel Nat A), fcnl_on_nat_onto R X
    obtain S h2 from h1
    define at h2
    set R : Rel A Nat := least_witness (invRel S)
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of fcnl_on R X
      define
      fix x
      assume h3
      exists_unique
      · -- Existence
        obtain p h4 from h2.right x h3
        set W : Set Nat := { n : Nat | S n x }
        have h5 : ∃ (n : Nat), n ∈ W := by
          apply Exists.intro p
          define
          exact h4
          done
        obtain n h6 from well_ord_princ W h5
        apply Exists.intro n
        define
        apply And.intro
        · -- Proof of InvRel S x n
          define
          exact h6.left
          done
        · -- Proof of least
          fix m
          assume h7
          define at h7
          exact h6.right m h7
          done
        done
      · -- Uniqueness
        fix n1; fix n2
        assume h4; assume h5
        define at h4; define at h5
        have h6 := h4.right n2 h5.left
        have h7 := h5.right n1 h4.left
        linarith
        done
      done
    · -- Proof of one-to-one
      fix x1; fix x2; fix n
      assume h3; assume h4; assume h5; assume h6
      define at h5
      define at h6
      have h7 := h5.left
      have h8 := h6.left
      define at h7
      define at h8
      have h9 := And.intro h3 h7
      have h10 := And.intro h4 h8
      obtain x h11 h12 from h2.left n
      exact h12 x1 x2 h9 h10
      done
    done
  done
-/

def restrict_to {A : Type} (S : Rel A Nat) (X : Set A) (x : A) (n : Nat) : Prop :=
  x ∈ X ∧ S x n

theorem Theorem_8_1_5_3_to_1 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X) :
    ctble X := by
  obtain S h2 from h1
  define at h2
  set Y : Set Nat := { n : Nat | ∃ x ∈ X, S x n }
  have h3 : equinum X Y := by
    set R : Rel A Nat := restrict_to S X
    define
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of rel_on R X Y
      define
      fix x; fix n
      assume h3
      define at h3
      apply And.intro h3.left
      define
      apply Exists.intro x
      exact h3
      done
    · --
      apply And.intro
      · -- Proof of fcnl_on R X
        define
        fix x
        assume h3
        have h4 := h2.left
        define at h4
        obtain y h5 h6 from h4 x h3
        exists_unique
        · -- Existence
          apply Exists.intro y
          define
          exact And.intro h3 h5
          done
        · -- Uniqueness
          fix y1; fix y2
          assume h7; assume h8
          define at h7; define at h8
          exact h6 y1 y2 h7.right h8.right
          done
        done
      · -- Proof of fcnl_on (invRel R) Y
        define
        fix n
        assume h3
        define at h3
        obtain x h4 from h3
        exists_unique
        · -- Existence
          apply Exists.intro x
          define
          exact h4
          done
        · -- Uniqueness
          fix x1; fix x2
          assume h5; assume h6
          define at h5; define at h6
          exact h2.right x1 x2 n h5.left h6.left h5.right h6.right
          done
        done
      done
    done
  have h4 : equinum Y X := Theorem_8_1_3_2 h3
  have h5 := subset_nat_ctble Y
  define
  define at h5
  by_cases on h5
  · -- Case 1. h5 : finite Y
    apply Or.inl
    define at h5; define
    obtain n h6 from h5
    apply Exists.intro n
    exact Theorem_8_1_3_3 h6 h4
    done
  · -- Case 2. h5 : denum Y
    apply Or.inr
    rewrite [denum_def]
    rewrite [denum_def] at h5
    exact Theorem_8_1_3_3 h5 h4
    done
  done

theorem Theorem_8_1_5_2 {A : Type} (X : Set A) :
    ctble X ↔ ∃ (R : Rel Nat A), unique_val_on_N R ∧ nat_rel_onto R X := by
  apply Iff.intro
  · -- (→)
    assume h1
    exact Theorem_8_1_5_1_to_2 h1
    done
  · -- (←)
    assume h1
    have h2 := Theorem_8_1_5_2_to_3 h1
    exact Theorem_8_1_5_3_to_1 h2
    done
  done

theorem Theorem_8_1_5_3 {A : Type} (X : Set A) :
    ctble X ↔ ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  apply Iff.intro
  · -- (→)
    assume h1
    have h2 := Theorem_8_1_5_1_to_2 h1
    exact Theorem_8_1_5_2_to_3 h2
    done
  · -- (←)
    assume h1
    exact Theorem_8_1_5_3_to_1 h1
    done
  done

theorem Exercise_6_1_16a1 : ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

theorem Exercise_6_1_16a2 : ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := sorry

def fnz (n : Nat) : Int := if 2 ∣ n then ↑(n / 2) else -↑((n + 1) / 2)

def fzn (a : Int) : Nat := if a ≥ 0 then 2 * Int.toNat a else 2 * Int.toNat (-a) - 1

lemma fnz_2dvd {n : Nat} (h : 2 ∣ n) : fnz n = ↑(n / 2) := by
  define : fnz n
  rewrite [if_pos h]
  rfl
  done

lemma fnz_not_2dvd {n : Nat} (h : ¬2 ∣ n) : fnz n = -↑((n + 1) / 2) := by
  define : fnz n
  rewrite [if_neg h]
  rfl
  done

lemma fnz_even (k : Nat) : fnz (2 * k) = ↑k := by
  have h1 : 2 ∣ 2 * k := by
    apply Exists.intro k
    rfl
    done
  have h2 : 2 > 0 := by norm_num
  rewrite [fnz_2dvd h1, Nat.mul_div_cancel_left k h2]
  rfl
  done

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := by
  have h1 : nat_odd (2 * k + 1) := by
    define
    apply Exists.intro k
    rfl
    done
  have h2 := Exercise_6_1_16a2 (2 * k + 1)
  demorgan at h2
  disj_syll h2 h1
  have h3 : ¬2 ∣ 2 * k + 1 := h2
  rewrite [fnz_not_2dvd h3]
  have h4 : 2 > 0 := by norm_num
  have h5 : (2 * k + 1 + 1) / 2 = k + 1 :=
    calc (2 * k + 1 + 1) / 2
      _ = 2 * (k + 1) / 2 := by ring
      _ =  k + 1 := Nat.mul_div_cancel_left (k + 1) h4
  rewrite [h5]
  rfl
  done

lemma fzn_nonneg {a : Int} (h : a ≥ 0) : fzn a = 2 * Int.toNat a := by
  define : fzn a
  rewrite [if_pos h]
  rfl
  done

lemma fzn_neg {a : Int} (h : ¬a ≥ 0) : fzn a = 2 * Int.toNat (-a) - 1 := by
  define : fzn a
  rewrite [if_neg h]
  rfl
  done

lemma fzn_nat (k : Nat) : fzn ↑k = 2 * k := by
  have h1 : (↑k : Int) ≥ 0 := Nat.cast_nonneg k
  rewrite [fzn_nonneg h1, Int.toNat_coe_nat]
  rfl
  done

lemma fzn_neg_succ_nat (k : Nat) : fzn (-↑(k + 1)) = 2 * k + 1 := by
  have h1 : ¬(-(↑(k + 1) : Int) ≥ 0) := by
    by_contra h1
    have h2 : k + 1 ≥ 1 := by linarith
    have h3 : (↑(k + 1) : Int) ≥ ↑(1 : Nat) := Nat.cast_le.rtl h2
    rewrite [Nat.cast_one] at h3
    have h4 : -(↑(k + 1) : Int) ≤ -1 := Int.neg_le_neg h3
    linarith 
    done
  rewrite [fzn_neg h1, neg_neg, Int.toNat_coe_nat]
  show 2 * (k + 1) - 1 = 2 * k + 1 :=
    calc 2 * (k + 1) - 1
      _ = 2 * k + 1 + 1 - 1 := by ring
      _ = 2 * k + 1 := Nat.add_sub_cancel _ _
  done

lemma fzn_fnz : fzn ∘ fnz = id := by
  apply funext
  fix n
  have h1 := Exercise_6_1_16a1 n
  by_cases on h1
  · -- Case 1. h1 : nat_even n
    obtain k h2 from h1
    rewrite [h2, comp_def, fnz_even, fzn_nat]
    rfl
    done
  · -- Case 2. h1 : nat_odd n
    obtain k h2 from h1
    rewrite [h2, comp_def, fnz_odd, fzn_neg_succ_nat]
    rfl
    done
  done

lemma int_eq_nat_or_neg_succ (a : Int) : (∃ (k : Nat), a = ↑k) ∨ ∃ (k : Nat), a = -↑(k + 1) := by
  by_cases h1 : 0 ≤ a
  · -- Case 1. h1 : 0 ≤ a
    apply Or.inl
    exact Int.eq_ofNat_of_zero_le h1
    done
  · -- Case 2. h1 : ¬0 ≤ a
    have h2 : 0 < -a := by linarith
    apply Or.inr
    obtain k h3 from Int.eq_succ_of_zero_lt h2
    apply Exists.intro k
    rewrite [←h3, neg_neg]
    rfl
    done
  done

lemma fnz_fzn : fnz ∘ fzn = id  := by
  apply funext
  fix a : Int
  have h1 := int_eq_nat_or_neg_succ a
  by_cases on h1
  · -- Case 1. h1 : ∃ (k : Nat), a = ↑k
    obtain k h2 from h1
    rewrite [h2, comp_def, fzn_nat, fnz_even]
    rfl
    done
  · -- Case 2. h1 : ∃ (k : Nat), a = -↑(k + 1)
    obtain k h2 from h1
    rewrite [h2, comp_def, fzn_neg_succ_nat, fnz_odd]
    rfl
    done
  done

example : one_to_one fnz := by
  apply Theorem_5_3_3_1 fnz
  exact Exists.intro fzn fzn_fnz
  done

example : onto fnz := by
  apply Theorem_5_3_3_2 fnz
  exact Exists.intro fzn fnz_fzn
  done

def tri (k : Nat) : Nat := k * (k + 1) / 2

/- Don't need??
def lt (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | m + 1 => if tri (lt m + 1) ≤ m + 1 then lt m + 1 else lt m
-/

def f (a b : Nat) := tri (a + b) + b

lemma tri_even (j : Nat) : tri (2 * j) = j * (2 * j + 1) :=
  calc tri (2 * j)
    _ = (2 * j) * (2 * j + 1) / 2 := by rfl
    _ = 2 * (j * (2 * j + 1)) / 2 := by ring
    _ = j * (2 * j + 1) := Nat.mul_div_cancel_left _ two_pos

lemma tri_odd (j : Nat) : tri (2 * j + 1) = (2 * j + 1) * (j + 1) :=
  calc tri (2 * j + 1)
    _ = (2 * j + 1) * (2 * j + 1 + 1) / 2 := by rfl
    _ = 2 * ((2 * j + 1) * (j + 1)) / 2 := by ring
    _ = (2 * j + 1) * (j + 1) := Nat.mul_div_cancel_left _ two_pos

lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := by
  have h1 : nat_even k ∨ nat_odd k := Exercise_6_1_16a1 k
  by_cases on h1
  · -- Case 1. h1 : nat_even k
    obtain j h2 from h1
    rewrite [h2]
    exact
      calc tri (2 * j + 1)
        _ = (2 * j + 1) * (j + 1) := tri_odd j
        _ = j * (2 * j + 1) + 2 * j + 1 := by ring
        _ = tri (2 * j) + 2 * j + 1 := by rw [tri_even]
    done
  · -- Case 2. h1 : nat_odd k
    obtain j h2 from h1
    rewrite [h2]
    exact
      calc tri (2 * j + 1 + 1)
        _ = tri (2 * (j + 1)) := by ring
        _ = (j + 1) * (2 * (j + 1) + 1) := tri_even (j + 1)
        _ = (2 * j + 1) * (j + 1) + (2 * j + 1) + 1 := by ring
        _ = tri (2 * j + 1) + (2 * j + 1) + 1 := by rw [tri_odd]
    done
  done

lemma tri_incr (j : Nat) : ∀ k ≥ j + 1, tri j + j + 1 ≤ tri k := by
  by_induc
  · -- Base Case
    rewrite [tri_step]
    linarith
    done
  · -- Induction Step
    fix k
    assume ih
    assume h1
    rewrite [tri_step]
    linarith
    done
  done

lemma le_of_f_eq {a1 b1 a2 b2 : Nat} (h1 : f a1 b1 = f a2 b2) : a1 + b1 ≤ a2 + b2 := by
  have h2 : tri (a1 + b1) + b1 = tri (a2 + b2) + b2 := h1
  by_contra h3
  have h4 : a2 + b2 + 1 ≤ a1 + b1 := by linarith
  have h5 := tri_incr (a2 + b2) (a1 + b1) h4
  have h6 : f a2 b2 < f a1 b1 :=
    calc f a2 b2
      _ = tri (a2 + b2) + b2 := by rfl
      _ < tri (a2 + b2) + (a2 + b2) + 1 := by linarith
      _ ≤ tri (a1 + b1) := h5
      _ ≤ tri (a1 + b1) + b1 := by linarith
      _ = f a1 b1 := by rfl
  linarith
  done

lemma f_one_one {a1 b1 a2 b2 : Nat} (h1 : f a1 b1 = f a2 b2) : a1 = a2 ∧ b1 = b2 := by
  have h2 := le_of_f_eq h1
  have h3 := le_of_f_eq h1.symm
  have h4 : a1 + b1 = a2 + b2 := by linarith
  have h5 : tri (a1 + b1) + b1 = tri (a2 + b2) + b2 := h1
  rewrite [h4] at h5
  have h6 : b1 = b2 := Nat.add_left_cancel h5
  rewrite [h6] at h4
  have h7 : a1 = a2 := Nat.add_right_cancel h4
  exact And.intro h7 h6
  done

lemma f_onto : ∀ (n : Nat), ∃ (a b : Nat), f a b = n := by
  by_induc
  · -- Base Case
    apply Exists.intro 0
    apply Exists.intro 0
    rfl
    done
  · -- Induction Step
    fix n
    assume ih
    obtain a h1 from ih
    obtain b h2 from h1
    by_cases h3 : a = 0
    · -- Case 1. h3 : a = 0
      apply Exists.intro (b + 1)
      apply Exists.intro 0
      rewrite [h3, f] at h2
      rewrite [f]
      have h4 := tri_step b
      exact
        calc tri (b + 1 + 0)
          _ = tri b + b + 1 := h4
          _ = tri (0 + b) + b + 1 := by ring
          _ = n + 1 := by rw [h2]
      done
    · -- Case 2. h3 : a ≠ 0
      obtain k (h4 : a = k + 1) from Nat.exists_eq_succ_of_ne_zero h3
      apply Exists.intro k
      apply Exists.intro (b + 1)
      exact
        calc f k (b + 1)
          _ = tri (k + (b + 1)) + (b + 1) := by rfl
          _ = tri (k + 1 + b) + b + 1 := by ring
          _ = tri (a + b) + b + 1 := by rw [h4]
          _ = f a b + 1 := by rfl
          _ = n + 1 := by rw [h2]
      done
    done
  done

-- *** Try using subtypes

def subtype {A : Type} (X : Set A) : Type := { x : A // x ∈ X }

def equinum2 {A B : Type} (X : Set A) (Y : Set B) : Prop :=
  ∃ (f : (subtype X) → (subtype Y)), one_to_one f ∧ onto f

lemma n_lt_n1 (n : Nat) : n < n + 1 := by linarith

lemma j_lt_n1 {j n : Nat} (h : j ∈ I n) : j < n + 1 := by define at h; linarith

def last_elt (n : Nat) : subtype (I (n + 1)) := ⟨n, n_lt_n1 n⟩ 

def embed_I {n : Nat} (j : subtype (I n)) : subtype (I (n + 1)) := ⟨j.val, j_lt_n1 j.property⟩

lemma rem_one_lemma1 {n : Nat} {A : Type} {X : Set A} (f : (subtype (I (n + 1))) → (subtype X))
    (h1 : one_to_one f ∧ onto f) {k : subtype (I (n + 1))} {j : subtype (I n)} (h2 : j.val = k.val) :
    (f (last_elt n)).val ∈ X \ { (f k).val } := by
  define
  apply And.intro (f (last_elt n)).property
  define
  by_contra h3
  have h4 : f (last_elt n) = f k := Subtype.eq h3
  have h5 : last_elt n = k := h1.left (last_elt n) k h4
  have h6 : k.val < n :=
    calc k.val
      _ = j.val := h2.symm
      _ < n := j.property
  have h7 : k.val = n :=
    calc k.val
      _ = (last_elt n).val := by rw [h5]
      _ = n := by rfl
  linarith
  done

lemma rem_one_lemma2 {n : Nat} {A : Type} {X : Set A} (f : (subtype (I (n + 1))) → (subtype X))
    (h1 : one_to_one f ∧ onto f) {k : subtype (I (n + 1))} {j : subtype (I n)} (h2 : ¬j.val = k.val) :
    (f (embed_I j)).val ∈ X \ { (f k).val } := by
  define
  apply And.intro (f (embed_I j)).property
  define
  by_contra h3
  have h4 : f (embed_I j) = f k := Subtype.eq h3
  have h5 : embed_I j = k := h1.left (embed_I j) k h4
  have h6 : k.val = j.val :=
    calc k.val
      _ = (embed_I j).val := by rw [h5]
      _ = j.val := by rfl
  exact h2 h6.symm
  done

def rem_one {n : Nat} {A : Type} {X : Set A} (f : (subtype (I (n + 1))) → (subtype X))
    (h1 : one_to_one f ∧ onto f) (k : subtype (I (n + 1)))
    (j : subtype (I n)) : subtype (X \ {(f k).val}) := if h : j.val = k.val then
    ⟨(f (last_elt n)).val, rem_one_lemma1 f h1 h⟩
    else ⟨(f (embed_I j)).val, rem_one_lemma2 f h1 h⟩

lemma rem_one_k {n : Nat} {A : Type} {X : Set A} (f : (subtype (I (n + 1))) → (subtype X))
    (h1 : one_to_one f ∧ onto f) {k : subtype (I (n + 1))}
    {j : subtype (I n)} (h2 : j.val = k.val) :
    (rem_one f h1 k j).val = (f (last_elt n)).val := by
  define : rem_one f h1 k j
  rewrite [dif_pos h2]
  rfl
  done

lemma rem_one_not_k {n : Nat} {A : Type} {X : Set A} (f : (subtype (I (n + 1))) → (subtype X))
    (h1 : one_to_one f ∧ onto f) {k : subtype (I (n + 1))}
    {j : subtype (I n)} (h2 : ¬j.val = k.val) :
    (rem_one f h1 k j).val = (f (embed_I j)).val := by
  define : rem_one f h1 k j
  rewrite [dif_neg h2]
  rfl
  done

lemma rem_one_k_neq_not_k {n : Nat} {A : Type} {X : Set A} (f : subtype (I (n + 1)) → subtype X)
    (h1 : one_to_one f ∧ onto f) {k : subtype (I (n + 1))}
    {j1 j2 : subtype (I n)} (h2 : j1.val = k.val) (h3 : ¬j2.val = k.val) :
    rem_one f h1 k j1 ≠ rem_one f h1 k j2 := by
  by_contra h4
  have h5 : (rem_one f h1 k j1).val = (rem_one f h1 k j2).val := by rw [h4]
  rewrite [rem_one_k f h1 h2, rem_one_not_k f h1 h3] at h5
  have h6 : f (last_elt n) = f (embed_I j2) := Subtype.eq h5
  have h7 := h1.left (last_elt n) (embed_I j2) h6
  have h8 : j2.val = n :=
    calc j2.val
      _ = (embed_I j2).val := by rfl
      _ = (last_elt n).val := by rw [h7]
      _ = n := by rfl
  have h9 : j2.val < n := j2.property
  linarith
  done

lemma rem_one_one_one {A : Type} {X : Set A} {n : Nat} (f : subtype (I (n + 1)) → subtype X)
    (h1 : one_to_one f ∧ onto f) (k : subtype (I (n + 1))) :
    one_to_one (rem_one f h1 k) := by
  define
  fix x1; fix x2
  assume h2
  by_cases h3 : x1.val = k.val
  · -- Case 1. h3 : x1.val = k.val
    by_cases h4 : x2.val = k.val
    · -- Case 1.1. h4 : x2.val = k.val
      rewrite [←h4] at h3
      show x1 = x2 from Subtype.eq h3
      done
    · -- Case 1.2. h4 : ¬x2.val = k.val
      have h5 := rem_one_k_neq_not_k f h1 h3 h4
      exact absurd h2 h5
      done
    done
  · -- Case 2. h3 : ¬x1.val = k.val
    by_cases h4 : x2.val = k.val
    · -- Case 2.1. h4 : x2.val = k.val
      have h5 := rem_one_k_neq_not_k f h1 h4 h3
      exact absurd h2.symm h5
      done
    · -- Case 2.2. h4 : x2.val ≠ k.val
      have h5 : (rem_one f h1 k x1).val = (rem_one f h1 k x2).val := by rw [h2]
      rewrite [rem_one_not_k f h1 h3, rem_one_not_k f h1 h4] at h5
      have h6 : f (embed_I x1) = f (embed_I x2) := Subtype.eq h5
      have h7 := h1.left (embed_I x1) (embed_I x2) h6
      have h8 : x1.val = x2.val :=
        calc x1.val
          _ = (embed_I x1).val := by rfl
          _ = (embed_I x2).val := by rw [h7]
          _ = x2.val := by rfl
      exact Subtype.eq h8
      done
    done
  done

lemma rem_one_onto {A : Type} {X : Set A} {n : Nat} (f : subtype (I (n + 1)) → subtype X)
    (h1 : one_to_one f ∧ onto f) (k : subtype (I (n + 1))) :
    onto (rem_one f h1 k) := by
  define
  fix y
  by_cases h2 : y.val = (f (last_elt n)).val
  · -- Case 1. h2 : y.val = (f (last_elt n)).val
    have h3 : k.val ≠ n := by
      
      done
    done
  done