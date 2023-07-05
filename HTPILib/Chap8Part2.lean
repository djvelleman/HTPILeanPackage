import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false


--From exercises of Section 6.1
theorem Exercise_6_1_16a1 : ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

/- Section 8.1 -/
def fnz (n : Nat) : Int := if 2 ∣ n then ↑(n / 2) else -↑((n + 1) / 2)

#eval [fnz 0, fnz 1, fnz 2, fnz 3, fnz 4, fnz 5, fnz 6]
  --Answer: [0, -1, 1, -2, 2, -3, 3]

def fzn (a : Int) : Nat := if a ≥ 0 then 2 * Int.toNat a else 2 * Int.toNat (-a) - 1

#eval [fzn 0, fzn (-1), fzn 1, fzn (-2), fzn 2, fzn (-3), fzn 3]
  --Answer: [0, 1, 2, 3, 4, 5, 6]

lemma fnz_even (k : Nat) : fnz (2 * k) = ↑k := by
  have h1 : 2 ∣ 2 * k := by
    apply Exists.intro k
    rfl
    done
  have h2 : fnz (2 * k) = if 2 ∣ 2 * k then ↑(2 * k / 2)
    else -↑((2 * k + 1) / 2) := by rfl
  rewrite [if_pos h1] at h2  --h2 : fnz (2 * k) = ↑(2 * k / 2)
  have h3 : 0 < 2 := by linarith
  rewrite [Nat.mul_div_cancel_left k h3] at h2
  show fnz (2 * k) = ↑k from h2
  done

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := sorry

lemma fzn_nat (k : Nat) : fzn ↑k = 2 * k := by rfl

lemma fzn_neg_succ_nat (k : Nat) : fzn (-↑(k + 1)) = 2 * k + 1 := by rfl

lemma fzn_fnz : fzn ∘ fnz = id := by
  apply funext        --Goal : ∀ (x : Nat), (fzn ∘ fnz) x = id x
  fix n : Nat
  rewrite [comp_def]  --Goal : fzn (fnz n) = id n
  have h1 : nat_even n ∨ nat_odd n := Exercise_6_1_16a1 n
  by_cases on h1
  · -- Case 1. h1 : nat_even n
    obtain (k : Nat) (h2 : n = 2 * k) from h1
    rewrite [h2, fnz_even, fzn_nat]
    rfl
    done
  · -- Case 2. h1 : nat_odd n
    obtain (k : Nat) (h2 : n = 2 * k + 1) from h1
    rewrite [h2, fnz_odd, fzn_neg_succ_nat]
    rfl
    done
  done

lemma fnz_fzn : fnz ∘ fzn = id  := sorry

lemma fzn_one_one : one_to_one fzn := Theorem_5_3_3_1 fzn fnz fnz_fzn

lemma fzn_onto : onto fzn := Theorem_5_3_3_2 fzn fnz fzn_fnz

lemma fnz_one_one : one_to_one fnz := Theorem_5_3_3_1 fnz fzn fzn_fnz

lemma fnz_onto : onto fnz := Theorem_5_3_3_2 fnz fzn fnz_fzn

def tri (k : Nat) : Nat := k * (k + 1) / 2

def fnnn (p : Nat × Nat) : Nat := tri (p.fst + p.snd) + p.fst

lemma fnnn_def (a b : Nat) : fnnn (a, b) = tri (a + b) + a := by rfl

#eval [fnnn (0, 0), fnnn (0, 1), fnnn (1, 0), fnnn (0, 2), fnnn (1, 1)]
  --Answer: [0, 1, 2, 3, 4]

lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := sorry

lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := sorry

lemma le_of_fnnn_eq {a1 b1 a2 b2 : Nat}
    (h1 : fnnn (a1, b1) = fnnn (a2, b2)) : a1 + b1 ≤ a2 + b2 := by
  by_contra h2
  have h3 : a2 + b2 + 1 ≤ a1 + b1 := by linarith
  have h4 : fnnn (a2, b2) < fnnn (a1, b1) :=
    calc fnnn (a2, b2)
      _ = tri (a2 + b2) + a2 := by rfl
      _ < tri (a2 + b2) + (a2 + b2) + 1 := by linarith
      _ = tri (a2 + b2 + 1) := (tri_step _).symm
      _ ≤ tri (a1 + b1) := tri_incr h3
      _ ≤ tri (a1 + b1) + a1 := by linarith
      _ = fnnn (a1, b1) := by rfl
  linarith
  done

lemma fnnn_one_one : one_to_one fnnn := by
  fix (a1, b1) : Nat × Nat
  fix (a2, b2) : Nat × Nat
  assume h1 : fnnn (a1, b1) = fnnn (a2, b2)  --Goal : (a1, b1) = (a2, b2)
  have h2 : a1 + b1 ≤ a2 + b2 := le_of_fnnn_eq h1
  have h3 : a2 + b2 ≤ a1 + b1 := le_of_fnnn_eq h1.symm
  have h4 : a1 + b1 = a2 + b2 := by linarith
  rewrite [fnnn_def, fnnn_def, h4] at h1
    --h1 : tri (a2 + b2) + a1 = tri (a2 + b2) + a2
  have h6 : a1 = a2 := Nat.add_left_cancel h1
  rewrite [h6] at h4   --h4 : a2 + b1 = a2 + b2
  have h7 : b1 = b2 := Nat.add_left_cancel h4
  rewrite [h6, h7]
  rfl
  done

lemma fnnn_onto : onto fnnn := by
  define  --Goal : ∀ (y : Nat), ∃ (x : Nat × Nat), fnnn x = y
  by_induc
  · -- Base Case
    apply Exists.intro (0, 0)
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∃ (x : Nat × Nat), fnnn x = n
    obtain ((a, b) : Nat × Nat) (h1 : fnnn (a, b) = n) from ih
    by_cases h2 : b = 0
    · -- Case 1. h2 : b = 0
      apply Exists.intro (0, a + 1)
      show fnnn (0, a + 1) = n + 1 from
        calc fnnn (0, a + 1)
          _ = tri (0 + (a + 1)) + 0 := by rfl
          _ = tri (a + 1) := by ring
          _ = tri a + a + 1 := tri_step a
          _ = tri (a + 0) + a + 1 := by ring
          _ = fnnn (a, b) + 1 := by rw [h2, fnnn_def]
          _ = n + 1 := by rw [h1]
      done
    · -- Case 2. h2 : b ≠ 0
      obtain (k : Nat) (h3 : b = k + 1) from
        exists_eq_add_one_of_ne_zero h2
      apply Exists.intro (a + 1, k)
      show fnnn (a + 1, k) = n + 1 from
        calc fnnn (a + 1, k)
          _ = tri (a + 1 + k) + (a + 1) := by rfl
          _ = tri (a + (k + 1)) + a + 1 := by ring
          _ = tri (a + b) + a + 1 := by rw [h3]
          _ = fnnn (a, b) + 1 := by rfl
          _ = n + 1 := by rw [h1]
      done
    done
  done

lemma one_one_on_of_one_one {A B : Type} {f : A → B}
    (h : one_to_one f) (X : Set A) : one_one_on f X := by
  define
  fix x1 : A; fix x2 : A
  assume h1 : x1 ∈ X
  assume h2 : x2 ∈ X
  show f x1 = f x2 → x1 = x2 from h x1 x2
  done

lemma elt_Univ {A : Type} (a : A) :
    a ∈ Univ A := by trivial

theorem equinum_Univ {A B : Type} {f : A → B}
    (h1 : one_to_one f) (h2 : onto f) : Univ A ∼ Univ B := by
  have h3 : image f (Univ A) = Univ B := by
    apply Set.ext
    fix b : B
    apply Iff.intro
    · -- (→)
      assume h3 : b ∈ image f (Univ A)
      show b ∈ Univ B from elt_Univ b
      done
    · -- (←)
      assume h3 : b ∈ Univ B
      obtain (a : A) (h4 : f a = b) from h2 b
      apply Exists.intro a
      apply And.intro _ h4
      show a ∈ Univ A from elt_Univ a
      done
    done
  show Univ A ∼ Univ B from
    equinum_image (one_one_on_of_one_one h1 (Univ A)) h3
  done

theorem Z_equinum_N : Univ Int ∼ Univ Nat :=
  equinum_Univ fzn_one_one fzn_onto

theorem NxN_equinum_N : Univ (Nat × Nat) ∼ Univ Nat :=
  equinum_Univ fnnn_one_one fnnn_onto

def num_elts_below (X : Set Nat) (m s : Nat) : Prop :=
  match m with
    | 0 => s = 0
    | n + 1 => (n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)) ∨
                (n ∉ X ∧ num_elts_below X n s)

lemma neb_step (X : Set Nat) (n s : Nat) : num_elts_below X (n + 1) s ↔
    (n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)) ∨
      (n ∉ X ∧ num_elts_below X n s) := by rfl

lemma neb_step_elt {X : Set Nat} {n : Nat} (h1 : n ∈ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ 1 ≤ s ∧ num_elts_below X n (s - 1) := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h2 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1) ∨
      ¬n ∈ X ∧ num_elts_below X n s
    by_cases on h2
    · -- Case 1. h2 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)
      show 1 ≤ s ∧ num_elts_below X n (s - 1) from h2.right
      done
    · -- Case 2. h2 : ¬n ∈ X ∧ num_elts_below X n s
      show 1 ≤ s ∧ num_elts_below X n (s - 1) from absurd h1 h2.left
      done
    done
  · -- (←)
    assume h2 : 1 ≤ s ∧ num_elts_below X n (s - 1)
    apply Or.inl
    show n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1) from And.intro h1 h2
    done
  done

lemma neb_step_not_elt {X : Set Nat} {n : Nat} (h1 : n ∉ X) (s : Nat) :
    num_elts_below X (n + 1) s ↔ num_elts_below X n s := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h2 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1) ∨
      ¬n ∈ X ∧ num_elts_below X n s
    by_cases on h2
    · -- Case 1. h2 : n ∈ X ∧ 1 ≤ s ∧ num_elts_below X n (s - 1)
      show num_elts_below X n s from absurd h2.left h1
      done
    · -- Case 2. h2 : ¬n ∈ X ∧ num_elts_below X n s
      show num_elts_below X n s from h2.right
      done
    done
  · -- (←)
    assume h2 : num_elts_below X n s
    apply Or.inr
    show ¬n ∈ X ∧ num_elts_below X n s from And.intro h1 h2
    done
  done

lemma neb_exists (X : Set Nat) :
    ∀ (n : Nat), ∃ (s : Nat), num_elts_below X n s := by
  by_induc
  · -- Base Case
    apply Exists.intro 0
    define
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∃ (s : Nat), num_elts_below X n s
    obtain (t : Nat) (h1 : num_elts_below X n t) from ih
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
      show num_elts_below X n t from h1
      done
    done
  done

lemma neb_unique (X : Set Nat) : ∀ ⦃n : Nat⦄, ∀ ⦃s1 s2 : Nat⦄,
    num_elts_below X n s1 → num_elts_below X n s2 → s1 = s2 := by
  by_induc
  · -- Base Case
    fix s1 : Nat; fix s2 : Nat
    assume h1 : num_elts_below X 0 s1
    assume h2 : num_elts_below X 0 s2
    define at h1; define at h2  --h1 : s1 = 0; h2 : s2 = 0
    rewrite [h1, h2]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ ⦃s1 s2 : Nat⦄,
      num_elts_below X n s1 → num_elts_below X n s2 → s1 = s2
    fix s1 : Nat; fix s2 : Nat
    assume h1 : num_elts_below X (n + 1) s1
    assume h2 : num_elts_below X (n + 1) s2
    by_cases h3 : n ∈ X
    · -- Case 1. h3 : n ∈ X
      rewrite [neb_step_elt h3] at h1
      rewrite [neb_step_elt h3] at h2
        --h1 : 1 ≤ s1 ∧ num_elts_below X n (s1 - 1)
        --h2 : 1 ≤ s1 ∧ num_elts_below X n (s1 - 1)
      have h4 : s1 - 1 = s2 - 1 := ih h1.right h2.right
      show s1 = s2 from
        calc s1
          _ = s1 - 1 + 1 := (Nat.sub_add_cancel h1.left).symm
          _ = s2 - 1 + 1 := by rw [h4]
          _ = s2 := Nat.sub_add_cancel h2.left
      done
    · -- Case 2. h3 : n ∉ X
      rewrite [neb_step_not_elt h3] at h1 --h1 : num_elts_below X n s1
      rewrite [neb_step_not_elt h3] at h2 --h2 : num_elts_below X n s2
      show s1 = s2 from ih h1 h2
      done
    done
  done

def enum (X : Set Nat) (s n : Nat) : Prop := n ∈ X ∧ num_elts_below X n s

lemma neb_increase {X : Set Nat} {n s : Nat} (h1 : enum X s n) :
    ∀ ⦃m : Nat⦄, m ≥ n + 1 → ∀ ⦃t : Nat⦄, num_elts_below X m t → s < t := by
  by_induc
  · -- Base Case
    define at h1
    fix t
    assume h2
    rewrite [neb_step_elt h1.left] at h2
    have h3 := neb_unique X h1.right h2.right
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
      have h5 := ih h3.right
      show s < t from
        calc s
          _ < t - 1 := h5
          _ ≤ t := Nat.sub_le _ _
      done
    · -- Case 2. h4 : m ∉ X
      rewrite [neb_step_not_elt h4] at h3
      exact ih h3
      done
    done
  done

lemma enum_not_skip {X : Set Nat} : ∀ ⦃m s : Nat⦄, num_elts_below X m s →
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
      have h3 := ih h1.right
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
        exact ih h1.right t h7
        done
      done
    · -- Case 2. h2 : m ∉ X
      rewrite [neb_step_not_elt h2] at h1
      exact ih h1
      done
    done
  done

lemma enum_le {X : Set Nat} {t n1 n2 : Nat}
    (h1 : enum X t n1) (h2 : enum X t n2) : n1 ≤ n2 := by
  by_contra h3
  have h4 : n2 + 1 ≤ n1 := by linarith
  define at h1
  have h5 := neb_increase h2 h4 h1.right
  linarith
  done

lemma enum_unique (X : Set Nat) (t : Nat) :
    ∀ ⦃n1 n2 : Nat⦄, enum X t n1 → enum X t n2 → n1 = n2 := by
  fix n1; fix n2
  assume h1; assume h2
  have h3 : n1 ≤ n2 := enum_le h1 h2
  have h4 : n2 ≤ n1 := enum_le h2 h1
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
    exact neb_unique X h2.right h3.right
    done
  done

lemma bdd_subset_nat_match {X : Set Nat} {m s : Nat}
    (h1 : ∀ (n : Nat), n ∈ X → n < m) (h2 : num_elts_below X m s) :
    matching (enum X) (I s) X := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix t; fix n
    assume h3
    have h4 := neb_increase h3
    define at h3
    apply And.intro _ h3.left
    define
    have h5 := h1 n h3.left
    have h6 : m ≥ n + 1 := by linarith
    exact h4 h6 h2
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
        exact enum_not_skip h2 t h3
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

lemma bdd_subset_nat {X : Set Nat} {m s : Nat}
    (h1 : ∀ (n : Nat), n ∈ X → n < m) (h2 : num_elts_below X m s) :
    I s ∼ X := Exists.intro (enum X) (bdd_subset_nat_match h1 h2)

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
      have h5 := enum_not_skip h4
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
      have h8 := neb_increase h4 h6.right h7
      have h9 : s + 1 < t ∨ s + 1 = t := Nat.lt_or_eq_of_le h8
      by_cases on h9
      · -- Case 1. h9 : s + 1 < t
        exact enum_not_skip h7 (s + 1) h9
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

lemma unbdd_subset_nat_match {X : Set Nat}
    (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ n ≥ m) :
    matching (enum X) (Univ Nat) X := by
  define
  apply And.intro
  · -- Proof of rel_within
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

lemma unbdd_subset_nat {X : Set Nat}
    (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ n ≥ m) :
    denum X := Exists.intro (enum X) (unbdd_subset_nat_match h1)

lemma subset_nat_ctble (X : Set Nat) : ctble X := by
  define          --Goal : finite X ∨ denum X
  by_cases h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ X → n < m
  · -- Case 1. h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ X → n < m
    apply Or.inl  --Goal : finite X
    obtain (m : Nat) (h2 : ∀ (n : Nat), n ∈ X → n < m) from h1
    obtain (s : Nat) (h3 : num_elts_below X m s) from neb_exists X m
    apply Exists.intro s
    show I s ∼ X from bdd_subset_nat h2 h3
    done
  · -- Case 2. h1 : ¬∃ (m : Nat), ∀ (n : Nat), n ∈ X → n < m
    apply Or.inr  --Goal : denum X
    push_neg at h1
      --This tactic converts h1 to ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ m ≤ n
    show denum X from unbdd_subset_nat h1
    done
  done

lemma ctble_of_equinum_ctble {A B : Type} {X : Set A} {Y : Set B}
    (h1 : X ∼ Y) (h2 : ctble X) : ctble Y := sorry

lemma ctble_iff_equinum_set_nat {A : Type} (X : Set A) : 
    ctble X ↔ ∃ (I : Set Nat), I ∼ X := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble X
    define at h1  --h1 : finite X ∨ denum X
    by_cases on h1
    · -- Case 1. h1 : finite X
      define at h1  --h1 : ∃ (n : Nat), I n ∼ X
      obtain (n : Nat) (h2 : I n ∼ X) from h1
      show ∃ (I : Set Nat), I ∼ X from Exists.intro (I n) h2
      done
    · -- Case 2. h1 : denum X
      rewrite [denum_def] at h1  --h1 : Univ Nat ∼ X
      show ∃ (I : Set Nat), I ∼ X from Exists.intro (Univ Nat) h1
      done
    done
  · -- (←)
    assume h1 : ∃ (I : Set Nat), I ∼ X
    obtain (I : Set Nat) (h2 : I ∼ X) from h1
    have h3 : ctble I := subset_nat_ctble I
    show ctble X from ctble_of_equinum_ctble h2 h3
    done
  done

def unique_val_on_N {A : Type} (R : Rel Nat A) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃x1 x2 : A⦄, R n x1 → R n x2 → x1 = x2

def nat_rel_onto {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ X → ∃ (n : Nat), R n x

def fcnl_onto_from_nat {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  unique_val_on_N R ∧ nat_rel_onto R X

theorem Theorem_8_1_5_1_to_2 {A : Type} {X : Set A} (h1 : ctble X) :
    ∃ (R : Rel Nat A), fcnl_onto_from_nat R X := by
  rewrite [ctble_iff_equinum_set_nat] at h1
  obtain (I : Set Nat) (h2 : I ∼ X) from h1
  obtain (R : Rel Nat A) (h3 : matching R I X) from h2
  define at h3
    --h3 : rel_within R I X ∧ fcnl_on R I ∧ fcnl_on (invRel R) X
  apply Exists.intro R
  define  --Goal : unique_val_on_N R ∧ nat_rel_onto R X
  apply And.intro
  · -- Proof of unique_val_on_N R
    define
    fix n : Nat; fix x1 : A; fix x2 : A
    assume h4 : R n x1
    assume h5 : R n x2      --Goal : x1 = x2
    have h6 : n ∈ I ∧ x1 ∈ X := h3.left h4
    show x1 = x2 from fcnl_unique h3.right.left h6.left h4 h5
    done
  · -- Proof of nat_rel_onto R X
    define
    fix x : A
    assume h4 : x ∈ X  --Goal : ∃ (n : Nat), R n x
    show ∃ (n : Nat), R n x from fcnl_exists h3.right.right h4
    done
  done

def fcnl_one_one_to_nat {A : Type} (R : Rel A Nat) (X : Set A) : Prop :=
  fcnl_on R X ∧ ∀ ⦃x1 x2 : A⦄ ⦃n : Nat⦄,
    (x1 ∈ X ∧ R x1 n) → (x2 ∈ X ∧ R x2 n) → x1 = x2

def least_rel_to {A : Type} (S : Rel Nat A) (x : A) (n : Nat) : Prop :=
  S n x ∧ ∀ (m : Nat), S m x → n ≤ m

lemma exists_least_rel_to {A : Type} {S : Rel Nat A} {x : A}
    (h1 : ∃ (n : Nat), S n x) : ∃ (n : Nat), least_rel_to S x n := by
  set W : Set Nat := { n : Nat | S n x }
  have h2 : ∃ (n : Nat), n ∈ W := h1
  show ∃ (n : Nat), least_rel_to S x n from well_ord_princ W h2
  done

theorem Theorem_8_1_5_2_to_3 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel Nat A), fcnl_onto_from_nat R X) :
    ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  obtain (S : Rel Nat A) (h2 : fcnl_onto_from_nat S X) from h1
  define at h2  --h2 : unique_val_on_N S ∧ nat_rel_onto S X
  set R : Rel A Nat := least_rel_to S
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of fcnl_on R X
    define
    fix x : A
    assume h4 : x ∈ X  --Goal : ∃! (y : Nat), R x y
    exists_unique
    · -- Existence
      have h5 : ∃ (n : Nat), S n x := h2.right h4
      show ∃ (n : Nat), R x n from exists_least_rel_to h5
      done
    · -- Uniqueness
      fix n1 : Nat; fix n2 : Nat
      assume h5 : R x n1
      assume h6 : R x n2      --Goal : n1 = n2
      define at h5    --h5 : S n1 x ∧ ∀ (m : Nat), S m x → n1 ≤ m
      define at h6    --h6 : S n2 x ∧ ∀ (m : Nat), S m x → n2 ≤ m
      have h7 : n1 ≤ n2 := h5.right n2 h6.left
      have h8 : n2 ≤ n1 := h6.right n1 h5.left
      linarith
      done
    done
  · -- Proof of one-to-one
    fix x1 : A; fix x2 : A; fix n : Nat
    assume h4 : x1 ∈ X ∧ R x1 n
    assume h5 : x2 ∈ X ∧ R x2 n
    have h6 : R x1 n := h4.right
    have h7 : R x2 n := h5.right
    define at h6   --h6 : S n x1 ∧ ∀ (m : Nat), S m x1 → n ≤ m
    define at h7   --h7 : S n x2 ∧ ∀ (m : Nat), S m x2 → n ≤ m
    show x1 = x2 from h2.left h6.left h7.left
    done
  done

def restrict_to {A B : Type} (S : Rel A B) (X : Set A)
  (x : A) (y : B) : Prop := x ∈ X ∧ S x y

theorem Theorem_8_1_5_3_to_1 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X) :
    ctble X := by
  obtain (S : Rel A Nat) (h2 : fcnl_one_one_to_nat S X) from h1
  define at h2  --h2 : fcnl_on S X ∧ ∀ ⦃x1 x2 : A⦄ ⦃n : Nat⦄,
                --x1 ∈ X ∧ S x1 n → x2 ∈ X ∧ S x2 n → x1 = x2
  rewrite [ctble_iff_equinum_set_nat]  --Goal : ∃ (I : Set Nat), I ∼ X
  set R : Rel Nat A := invRel (restrict_to S X)
  set I : Set Nat := { n : Nat | ∃ (x : A), R n x }
  apply Exists.intro I
  define        --Goal : ∃ (R : Rel Nat A), matching R I X
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of rel_within R I X
    define
    fix n : Nat; fix x : A
    assume h3 : R n x   --Goal : n ∈ I ∧ x ∈ X
    apply And.intro
    · -- Proof that n ∈ I
      define            --Goal : ∃ (x : A), R n x
      show ∃ (x : A), R n x from Exists.intro x h3
      done
    · -- Proof that x ∈ X
      define at h3      --h3 : x ∈ X ∧ S x n
      show x ∈ X from h3.left
      done
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R I
      define
      fix n : Nat
      assume h3 : n ∈ I   --Goal : ∃! (y : A), R n y
      exists_unique
      · -- Existence
        define at h3      --h3 : ∃ (x : A), R n x
        show ∃ (y : A), R n y from h3
        done
      · -- Uniqueness
        fix x1 : A; fix x2 : A
        assume h4 : R n x1
        assume h5 : R n x2
        define at h4      --h4 : x1 ∈ X ∧ S x1 n; 
        define at h5      --h5 : x2 ∈ X ∧ S x2 n
        show x1 = x2 from h2.right h4 h5
        done
      done
    · -- Proof of fcnl_on (invRel R) X
      define
      fix x : A
      assume h3 : x ∈ X  --Goal : ∃! (y : Nat), invRel R x y
      exists_unique
      · -- Existence
        obtain (y : Nat) (h4 : S x y) from fcnl_exists h2.left h3
        apply Exists.intro y
        define
        show x ∈ X ∧ S x y from And.intro h3 h4
        done
      · -- Uniqueness
        fix n1 : Nat; fix n2 : Nat
        assume h4 : invRel R x n1
        assume h5 : invRel R x n2  --Goal : n1 = n2
        define at h4     --h4 : x ∈ X ∧ S x n1
        define at h5     --h5 : x ∈ X ∧ S x n2
        show n1 = n2 from fcnl_unique h2.left h3 h4.right h5.right
        done
      done
    done
  done

theorem Theorem_8_1_5_2 {A : Type} (X : Set A) :
    ctble X ↔ ∃ (R : Rel Nat A), fcnl_onto_from_nat R X := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble X
    show ∃ (R : Rel Nat A), fcnl_onto_from_nat R X from
      Theorem_8_1_5_1_to_2 h1
    done
  · -- (←)
    assume h1 : ∃ (R : Rel Nat A), fcnl_onto_from_nat R X
    have h2 : ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X :=
      Theorem_8_1_5_2_to_3 h1
    show ctble X from Theorem_8_1_5_3_to_1 h2
    done
  done

theorem Theorem_8_1_5_3 {A : Type} (X : Set A) :
    ctble X ↔ ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble X
    have h2 : ∃ (R : Rel Nat A), fcnl_onto_from_nat R X :=
      Theorem_8_1_5_1_to_2 h1
    show ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X from
      Theorem_8_1_5_2_to_3 h2
    done
  · -- (←)
    assume h1 : ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X
    show ctble X from Theorem_8_1_5_3_to_1 h1
    done
  done

def fqn (q : Rat) : Nat := fnnn (fzn q.num, q.den)

lemma fqn_def (q : Rat) : fqn q = fnnn (fzn q.num, q.den) := by rfl

lemma fqn_one_one : one_to_one fqn := by
  define
  fix q1 : Rat; fix q2 : Rat
  assume h1 : fqn q1 = fqn q2
  rewrite [fqn_def, fqn_def] at h1
    --h1 : fnnn (fzn q1.num, q1.den) = fnnn (fzn q2.num, q2.den)
  have h2 : (fzn q1.num, q1.den) = (fzn q2.num, q2.den) :=
    fnnn_one_one _ _ h1
  have h3 : fzn q1.num = fzn q2.num ∧ q1.den = q2.den :=
    Prod.mk.inj h2
  have h4 : q1.num = q2.num := fzn_one_one _ _ h3.left
  show q1 = q2 from Rat.ext q1 q2 h4 h3.right
  done

lemma image_fqn_unbdd :
    ∀ (m : Nat), ∃ (n : Nat), n ∈ image fqn (Univ Rat) ∧ n ≥ m := by
  fix m : Nat
  set n : Nat := fqn ↑m
  apply Exists.intro n
  apply And.intro
  · -- Proof that n ∈ image fqn (Univ Rat)
    define
    apply Exists.intro ↑m
    apply And.intro (elt_Univ (↑m : Rat))
    rfl
    done
  · -- Proof that n ≥ m
    show n ≥ m from
      calc n
        _ = tri (2 * m + 1) + 2 * m := by rfl
        _ ≥ m := by linarith
    done
  done

theorem Theorem_8_1_6 : denum (Univ Rat) := by
  set I : Set Nat := image fqn (Univ Rat)
  have h1 : Univ Nat ∼ I := unbdd_subset_nat image_fqn_unbdd
  have h2 : image fqn (Univ Rat) = I := by rfl
  have h3 : Univ Rat ∼ I :=
    equinum_image (one_one_on_of_one_one fqn_one_one (Univ Rat)) h2
  have h4 : I ∼ Univ Rat := Theorem_8_1_3_2 h3
  show denum (Univ Rat) from Theorem_8_1_3_3 h1 h4
  done

/- Section 8.1½ -/
lemma eq_zero_of_I_zero_equinum {n : Nat} (h1 : I 0 ∼ I n) : n = 0 := by
  rewrite [←numElts_def, zero_elts_iff_empty] at h1
    --h1 : empty (I n)
  contradict h1 with h2       --Goal : ∃ (x : Nat), x ∈ I n
  apply Exists.intro 0
  define
  show 0 < n from Nat.pos_of_ne_zero h2
  done

theorem eq_of_I_equinum : ∀ ⦃m n : Nat⦄, I m ∼ I n → m = n := by
  by_induc
  · -- Base Case
    fix n : Nat
    assume h1 : I 0 ∼ I n
    show 0 = n from (eq_zero_of_I_zero_equinum h1).symm
    done
  · -- Induction Step
    fix m : Nat
    assume ih : ∀ ⦃n : Nat⦄, I m ∼ I n → m = n
    fix n : Nat
    assume h1 : I (m + 1) ∼ I n      --Goal : m + 1 = n
    have h2 : n ≠ 0 := by
      by_contra h2
      have h3 : I n ∼ I (m + 1) := Theorem_8_1_3_2 h1
      rewrite [h2] at h3
      have h4 : m + 1 = 0 := eq_zero_of_I_zero_equinum h3
      linarith
      done
    obtain (k : Nat) (h3 : n = k + 1) from exists_eq_add_one_of_ne_zero h2
    rewrite [h3] at h1               --h1 : I (m + 1) ∼ I (k + 1)
    rewrite [h3]                     --Goal : m + 1 = k + 1
    have h4 : m ∈ I (m + 1) := I_max m
    have h5 : k ∈ I (k + 1) := I_max k
    have h6 : I (m + 1) \ {m} ∼ I (k + 1) \ {k} :=
      remove_one_equinum h1 h4 h5
    rewrite [I_diff, I_diff] at h6   --h6 : I m ∼ I k
    have h7 : m = k := ih h6
    rewrite [h7]
    rfl
    done
  done

theorem numElts_unique {A : Type} {X : Set A} {m n : Nat}
    (h1 : numElts X m) (h2 : numElts X n) : m = n := by
  rewrite [numElts_def] at h1      --h1 : I m ∼ X
  rewrite [numElts_def] at h2      --h2 : I n ∼ X
  have h3 : X ∼ I n := Theorem_8_1_3_2 h2
  have h4 : I m ∼ I n := Theorem_8_1_3_3 h1 h3
  show m = n from eq_of_I_equinum h4
  done

/- phi agrees with numElts -/
def Set_rp_below (m : Nat) : Set Nat := { n : Nat | rel_prime m n ∧ n < m }

lemma Set_rp_below_def (a m : Nat) :
    a ∈ Set_rp_below m ↔ rel_prime m a ∧ a < m := by rfl

lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (Set_rp_below m) k (num_rp_below m k) := by
  by_induc
  · -- Base Case
    assume h1
    rewrite [num_rp_below_base]
    define
    rfl
    done
  · -- Induction Step
    fix k
    assume ih
    assume h1
    have h2 : k ≤ m := by linarith
    by_cases h3 : rel_prime m k
    · -- Case 1. h3 : rel_prime m k
      have h4 : k ∈ Set_rp_below m := by
        define
        exact And.intro h3 h1
        done
      rewrite [num_rp_below_step_rp h3, neb_step_elt h4]
      rewrite [Nat.add_sub_cancel]
      apply And.intro _ (ih h2)
      linarith
      done
    · -- Case 2. h3 : ¬rel_prime m k
      have h4 : k ∉ Set_rp_below m := by
        define
        demorgan
        exact Or.inl h3
        done
      rewrite [num_rp_below_step_not_rp h3, neb_step_not_elt h4]
      exact ih h2
      done
    done
  done

lemma neb_phi (m : Nat) :
    num_elts_below (Set_rp_below m) m (phi m) := by
  rewrite [phi_def]
  have h1 : m ≤ m := by linarith
  show num_elts_below (Set_rp_below m) m (num_rp_below m m) from
    neb_nrpb m h1
  done

lemma phi_is_numElts (m : Nat) :
    numElts (Set_rp_below m) (phi m) := by
  rewrite [numElts_def]    --Goal : I (phi m) ∼ Set_rp_below m
  have h1 : ∀ (n : Nat), n ∈ Set_rp_below m → n < m := by
    fix n : Nat
    assume h2 : n ∈ Set_rp_below m
    define at h2
    show n < m from h2.right
    done
  have h2 : num_elts_below (Set_rp_below m) m (phi m) := neb_phi m
  show I (phi m) ∼ Set_rp_below m from bdd_subset_nat h1 h2
  done

lemma Lemma_7_4_7_aux {m n : Nat} {s t : Int}
    (h : s * m + t * n = 1) (a b : Nat) :
    t * n * a + s * m * b ≡ a (MOD m) := by
  define
  apply Exists.intro (s * (b - a))
  show t * n * a + s * m * b - a = m * (s * (b - a)) from
    calc t * n * a + s * m * b - a
      _ = (t * n - 1) * a + s * m * b := by ring
      _ = (t * n - (s * m + t * n)) * a + s * m * b := by rw [h]
      _ = m * (s * (b - a)) := by ring
  done

lemma Lemma_7_4_7 {m n : Nat} [NeZero m] [NeZero n]
    (h1 : rel_prime m n) (a b : Nat) :
    ∃ (r : Nat), r < m * n ∧ r ≡ a (MOD m) ∧ r ≡ b (MOD n) := by
  set s : Int := gcd_c1 m n
  set t : Int := gcd_c2 m n
  have h4 : s * m + t * n = gcd m n := gcd_lin_comb n m
  define at h1                      --h1 : gcd m n = 1
  rewrite [h1, Nat.cast_one] at h4  --h4 : s * m + t * n = 1
  set x : Int := t * n * a + s * m * b
  have h5 : x ≡ a (MOD m) := Lemma_7_4_7_aux h4 a b
  rewrite [add_comm] at h4          --h4 : t * n + s * m = 1
  have h6 : s * m * b + t * n * a ≡ b (MOD n) :=
    Lemma_7_4_7_aux h4 b a
  have h7 : s * m * b + t * n * a = x := by ring
  rewrite [h7] at h6                --h6 : x ≡ b (MOD n)
  have h8 : m * n ≠ 0 := mul_ne_zero (NeZero.ne m) (NeZero.ne n)
  rewrite [←neZero_iff] at h8       --h8 : NeZero (m * n)
  have h9 : 0 ≤ x % ↑(m * n) ∧ x % ↑(m * n) < ↑(m * n) ∧
    x ≡ x % ↑(m * n) (MOD m * n) := mod_cmpl_res (m * n) x
  have h10 : x % ↑(m * n) < ↑(m * n) ∧
    x ≡ x % ↑(m * n) (MOD m * n) := h9.right
  set r : Nat := Int.toNat (x % ↑(m * n))
  have h11 : x % ↑(m * n) = ↑r := (Int.toNat_of_nonneg h9.left).symm
  rewrite [h11, Nat.cast_lt] at h10 --h10 : r < m * n ∧ x ≡ r (MOD m * n)
  apply Exists.intro r
  apply And.intro h10.left
  have h12 : r ≡ x (MOD (m * n)) := congr_symm h10.right
  rewrite [Lemma_7_4_5 _ _ h1] at h12 --h12 : r ≡ x (MOD m) ∧ r ≡ x (MOD n)
  apply And.intro
  · -- Proof that r ≡ a (MOD m)
    show r ≡ a (MOD m) from congr_trans h12.left h5
    done
  · -- Proof that r ≡ b (MOD n)
    show r ≡ b (MOD n) from congr_trans h12.right h6
    done
  done

/- Theorem 8.1.2 -/
def Set_prod {A B : Type} (X : Set A) (Y : Set B) : Set (A × B) :=
  { (a, b) : A × B | a ∈ X ∧ b ∈ Y }

notation:75 X:75 " ×ₛ " Y:75 => Set_prod X Y

lemma Set_prod_def {A B : Type} (X : Set A) (Y : Set B) (a : A) (b : B) :
    (a, b) ∈ X ×ₛ Y ↔ a ∈ X ∧ b ∈ Y := by rfl

def Rel_prod {A B C D : Type} (R : Rel A B) (S : Rel C D)
  (p : A × C) (q : B × D) : Prop := R p.fst q.fst ∧ S p.snd q.snd

notation:75 R:75 " ×ᵣ " S:75 => Rel_prod R S

lemma Rel_prod_def {A B C D : Type} (R : Rel A B) (S : Rel C D)
    (a : A) (b : B) (c : C) (d : D) :
    (R ×ᵣ S) (a, c) (b, d) ↔ R a b ∧ S c d := by rfl

lemma prod_match {A B C D : Type}
    {U : Set A} {V : Set B} {W : Set C} {X : Set D}
    {R : Rel A B} {S : Rel C D}
    (h1 : matching R U V) (h2 : matching S W X) :
    matching (R ×ᵣ S) (U ×ₛ W) (V ×ₛ X) := sorry

theorem Theorem_8_1_2_1
    {A B C D : Type} {U : Set A} {V : Set B} {W : Set C} {X : Set D}
    (h1 : U ∼ V) (h2 : W ∼ X) : U ×ₛ W ∼ V ×ₛ X := by
  obtain (R : Rel A B) (h3 : matching R U V) from h1
  obtain (S : Rel C D) (h4 : matching S W X) from h2
  apply Exists.intro (R ×ᵣ S)
  show matching (R ×ᵣ S) (U ×ₛ W) (V ×ₛ X) from prod_match h3 h4
  done

-- Exercise from Section 6.4
/- Don't use this one
theorem quot_rem_unique (m q r q' r' : Nat)
    (h1 : m * q + r = m * q' + r') (h2 : r < m) (h3 : r' < m) :
    q = q' ∧ r = r' := sorry
-/

theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := sorry

def qr (n a : Nat) : Nat × Nat := (a / n, a % n)

lemma qr_def (n a : Nat) : qr n a = (a / n, a % n) := by rfl

lemma qr_one_one (n : Nat) : one_to_one (qr n) := by
  define
  fix a1 : Nat; fix a2 : Nat
  assume h1 : qr n a1 = qr n a2       --Goal : a1 = a2
  rewrite [qr_def, qr_def] at h1
  have h2 : a1 / n = a2 / n ∧ a1 % n = a2 % n := Prod.mk.inj h1
  show a1 = a2 from
    calc a1
      _ = n * (a1 / n) + a1 % n := (Nat.div_add_mod a1 n).symm
      _ = n * (a2 / n) + a2 % n := by rw [h2.left, h2.right]
      _ = a2 := Nat.div_add_mod a2 n
  done

lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := equinum_image
  (one_one_on_of_one_one (qr_one_one n) (I (m * n))) (qr_image m n)

/- Previous version
def qr (n : Nat) (p : Nat × Nat) : Nat := n * p.1 + p.2

lemma qr_def (n q r : Nat) : qr n (q, r) = n * q + r := by rfl

lemma qr_one_one_on (m n : Nat) : one_one_on (qr n) (I m ×ₛ I n) := by
  define
  fix (q1, r1); fix (q2, r2)
  assume h1
  assume h2
  assume h3
  define at h1; define at h2
  rewrite [I_def r1] at h1
  rewrite [I_def r2] at h2
  rewrite [qr_def, qr_def] at h3
  have h6 : q1 = q2 ∧ r1 = r2 := quot_rem_unique n q1 r1 q2 r2 h3 h1.right h2.right
  rewrite [h6.left, h6.right]
  rfl
  done

lemma qr_image (m n : Nat) : image (qr n) (I m ×ₛ I n) = I (m * n) := by
  apply Set.ext
  fix k
  apply Iff.intro
  · -- (→)
    assume h1
    define
    obtain ((q, r) : Nat × Nat) h2 from h1
    have h3 := h2.left
    have h4 := h2.right
    define at h3
    rewrite [I_def, I_def] at h3
    rewrite [qr_def] at h4
    have h5 : q + 1 ≤ m := h3.left
    exact
      calc k
        _ = n * q + r := h4.symm
        _ < n * q + n := by linarith
        _ = (q + 1) * n := by ring
        _ ≤ m * n := Nat.mul_le_mul_right _ h5
    done
  · -- (←)
    assume h1
    define at h1
    apply Exists.intro (k / n, k % n)
    apply And.intro
    · -- Proof that (k / n, k % n) ∈ I m ×ₛ I n
      define
      rewrite [I_def, I_def]
      rewrite [mul_comm] at h1
      apply And.intro (Nat.div_lt_of_lt_mul h1)
      have h2 : n ≠ 0 := by
        by_contra h2
        rewrite [h2] at h1
        linarith
        done
      have h3 : 0 < n := Nat.pos_of_ne_zero h2
      exact Nat.mod_lt k h3
      done
    · -- Proof that qr n (k / n, k % n) = k
      rewrite [qr_def]
      exact Nat.div_add_mod k n
      done
    done
  done

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := by
  have h : I m ×ₛ I n ∼ image (qr n) (I m ×ₛ I n) :=
    equinum_image (qr_one_one_on m n)
  rewrite [qr_image m n] at h
  show I (m * n) ∼ I m ×ₛ I n from Theorem_8_1_3_2 h
  done
-/

theorem numElts_prod {A B : Type} {X : Set A} {Y : Set B} {m n : Nat}
    (h1 : numElts X m) (h2 : numElts Y n) : numElts (X ×ₛ Y) (m * n) := by
  rewrite [numElts_def] at h1     --h1 : I m ∼ X
  rewrite [numElts_def] at h2     --h2 : I n ∼ Y
  rewrite [numElts_def]           --Goal : I (m * n) ∼ X ×ₛ Y
  have h3 : I m ×ₛ I n ∼ X ×ₛ Y := Theorem_8_1_2_1 h1 h2
  have h4 : I (m * n) ∼ I m ×ₛ I n := I_prod m n
  show I (m * n) ∼ X ×ₛ Y from Theorem_8_1_3_3 h4 h3
  done

/- Old version--function going other way
-- Exercise from Section 6.4
theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := sorry

def moddiv (m k : Nat) : Nat × Nat := (k % m, k / m)

lemma moddiv_def (m k : Nat) : moddiv m k = (k % m, k / m) := by rfl

lemma moddiv_r {m k r q} (h : moddiv m k = (r, q)) : r = k % m := by
  rewrite [moddiv_def] at h
  exact (Prod.mk.inj h).left.symm
  done

lemma moddiv_q {m k r q} (h : moddiv m k = (r, q)) : q = k / m := by
  rewrite [moddiv_def] at h
  exact (Prod.mk.inj h).right.symm
  done

lemma moddiv_one_one (m : Nat) : one_to_one (moddiv m) := by
  fix j; fix k
  assume h1
  exact
    calc j
      _ = m * (j / m) + j % m := (Nat.div_add_mod j m).symm
      _ = m * (moddiv m j).2 + (moddiv m j).1 := by rfl
      _ = m * (moddiv m k).2 + (moddiv m k).1 := by rw [h1]
      _ = m * (k / m) + k % m := by rfl
      _ = k := Nat.div_add_mod k m
  done

lemma moddiv_image (m n : Nat) : image (moddiv m) (I (m * n)) = I m ×ₛ I n := by
  apply Set.ext
  fix (r, q)
  apply Iff.intro
  · -- (→)
    assume h1
    define
    obtain k h2 from h1
    have h3 := h2.left
    define at h3
    have h4 : m ≠ 0 := by
      by_contra h4
      rewrite [h4] at h3
      linarith
      done
    have h5 : 0 < m := Nat.pos_of_ne_zero h4
    rewrite [moddiv_r h2.right, moddiv_q h2.right]
    apply And.intro
    · -- Proof that k % m ∈ I m
      define
      exact Nat.mod_lt k h5
      done
    · -- Proof that k / m ∈ I n
      define
      exact Nat.div_lt_of_lt_mul h3
      done
    done
  · -- (←)
    assume h1
    define at h1
    have h2 := h1.left
    have h3 := h1.right
    define at h2; define at h3
    apply Exists.intro (m * q + r)
    apply And.intro
    · -- Proof that m * q + r ∈ I (m * n)
      define
      have h4 : q + 1 ≤ n := h3
      exact
        calc m * q + r
          _ < m * q + m := Nat.add_lt_add_left h2 _
          _ = m * (q + 1) := by ring
          _ ≤ m * n := Nat.mul_le_mul_left _ h4
      done
    · -- Proof that moddiv m (m * q + r) = (r, q)
      set k : Nat := m * q + r
      have h4 : k = m * q + r := by rfl
      have h5 := div_mod_char m k q r h4 h2
      rewrite [h5.left, h5.right, moddiv_def]
      rfl
      done
    done
  done

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := by
  have h := equinum_image (one_one_on_of_one_one (moddiv_one_one m) (I (m * n)))
  rewrite [moddiv_image m n] at h
  exact h
  done
-/

/- Old version
theorem numElts_prod {A B : Type} {X : Set A} {m : Nat} (h1 : numElts X m) :
    ∀ ⦃n : Nat⦄ ⦃Y : Set B⦄, numElts Y n → numElts (X ×ₛ Y) (m * n) := by
  by_induc
  · -- Base Case
    fix Y
    assume h2
    rewrite [zero_elts_iff_empty] at h2
    have h3 : m * 0 = 0 := by norm_num
    rewrite [h3, zero_elts_iff_empty]
    exact Set_prod_empty X h2
    done
  · -- Induction Step
    fix n
    assume ih
    fix Y
    assume h2
    have h3 : n + 1 > 0 := by linarith
    obtain b h4 from nonempty_of_pos_numElts h2 h3
    set Y' : Set B := Y \ {b}
    have h5 : numElts Y' n := remove_one_numElts h2 h4
    have h6 := ih h5
    have h7 : numElts (X ×ₛ {b}) m := prod_singleton_numElts h1 b
    have h8 : empty (X ×ₛ {b} ∩ X ×ₛ Y') := by
      rewrite [Set_prod_inter]
      have h8 : empty ({b} ∩ Y'):= inter_diff_empty {b} Y
      exact Set_prod_empty X h8
      done
    have h9 := Theorem_8_1_7 h8 h7 h6
    have h10 : {b} ⊆ Y := by
      fix y
      assume h10
      define at h10
      rewrite [h10]
      exact h4
      done
    have h11 : {b} ∪ Y' = Y := union_diff h10
    rewrite [Set_prod_union, h11] at h9
    have h12 : m + m * n = m * (n + 1) := by ring
    rewrite [h12] at h9
    exact h9
    done
  done
-/

/- phi multiplicative -/


def mod_mod (m n a : Nat) : Nat × Nat := (a % m, a % n)

lemma mod_mod_def (m n a : Nat) : mod_mod m n a = (a % m, a % n) := by rfl

-- Next three are from Chapter 7 Exercises:
-- From Section 7.3 exercises
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

-- From Section 7.4 exercises
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

lemma left_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero m :=
  neZero_iff.rtl (left_ne_zero_of_mul h)

lemma right_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero n :=
  neZero_iff.rtl (right_ne_zero_of_mul h)

lemma mod_mod_one_one_on {m n : Nat} (h1 : rel_prime m n) :
    one_one_on (mod_mod m n) (Set_rp_below (m * n)) := by
  define
  fix a1 : Nat; fix a2 : Nat
  assume h2 : a1 ∈ Set_rp_below (m * n)
  assume h3 : a2 ∈ Set_rp_below (m * n)
  assume h4 : mod_mod m n a1 = mod_mod m n a2   --Goal : a1 = a2
  define at h2; define at h3
  rewrite [mod_mod_def, mod_mod_def] at h4
  have h5 : a1 % m = a2 % m ∧ a1 % n = a2 % n := Prod.mk.inj h4
  have h6 : m * n ≠ 0 := by linarith
  have h7 : NeZero m := left_NeZero_of_mul h6
  have h8 : NeZero n := right_NeZero_of_mul h6
  rewrite [←congr_iff_mod_eq, ←congr_iff_mod_eq] at h5
      --h5 : a1 ≡ a2 (MOD m) ∧ a1 ≡ a2 (MOD n)
  rewrite [←Lemma_7_4_5 _ _ h1] at h5  --h5 : a1 ≡ a2 (MOD m * n)
  rewrite [congr_iff_mod_eq] at h5     --h5 : a1 % (m * n) = a2 % (m * n)
  rewrite [Nat.mod_eq_of_lt h2.right, Nat.mod_eq_of_lt h3.right] at h5
  show a1 = a2 from h5
  done

lemma mod_elt_Set_rp_below {a m : Nat} [NeZero m] (h1 : rel_prime m a) :
    a % m ∈ Set_rp_below m := by
  define                  --Goal : rel_prime m (a % m) ∧ a % m < m
  rewrite [rel_prime_mod] --Goal : rel_prime m a ∧ a % m < m
  show rel_prime m a ∧ a % m < m from
    And.intro h1 (mod_nonzero_lt a (NeZero.ne m))
  done

lemma mod_mod_image {m n : Nat} (h1 : rel_prime m n) :
    image (mod_mod m n) (Set_rp_below (m * n)) =
      (Set_rp_below m) ×ₛ (Set_rp_below n) := by
  apply Set.ext
  fix (b, c) : Nat × Nat
  apply Iff.intro
  · -- (→)
    assume h2 : (b, c) ∈ image (mod_mod m n) (Set_rp_below (m * n))
    define at h2
    obtain (a : Nat)
      (h3 : a ∈ Set_rp_below (m * n) ∧ mod_mod m n a = (b, c)) from h2
    rewrite [Set_rp_below_def, mod_mod_def] at h3
    have h4 : rel_prime (m * n) a := h3.left.left
    rewrite [Lemma_7_4_6] at h4   --h4 : rel_prime m a ∧ rel_prime n a
    have h5 : a % m = b ∧ a % n = c := Prod.mk.inj h3.right
    define
    rewrite [←h5.left, ←h5.right]
      --Goal : a % m ∈ Set_rp_below m ∧ a % n ∈ Set_rp_below n
    have h6 : m * n ≠ 0 := by linarith
    have h7 : NeZero m := left_NeZero_of_mul h6
    have h8 : NeZero n := right_NeZero_of_mul h6
    apply And.intro
    · -- Proof that a % m ∈ Set_rp_below m
      show a % m ∈ Set_rp_below m from mod_elt_Set_rp_below h4.left
      done
    · -- Proof that a % n ∈ Set_rp_below n
      show a % n ∈ Set_rp_below n from mod_elt_Set_rp_below h4.right
      done
    done
  · -- (←)
    assume h2 : (b, c) ∈ Set_rp_below m ×ₛ Set_rp_below n
    rewrite [Set_prod_def, Set_rp_below_def, Set_rp_below_def] at h2
      --h2 : (rel_prime m b ∧ b < m) ∧ (rel_prime n c ∧ c < n)
    define
    have h3 : m ≠ 0 := by linarith
    have h4 : n ≠ 0 := by linarith
    rewrite [←neZero_iff] at h3
    rewrite [←neZero_iff] at h4
    obtain (a : Nat) (h5 : a < m * n ∧ a ≡ b (MOD m) ∧ a ≡ c (MOD n))
      from Lemma_7_4_7 h1 b c
    apply Exists.intro a
    apply And.intro
    · -- Proof of a ∈ Set_rp_below (m * n)
      define                  --Goal : rel_prime (m * n) a ∧ a < m * n
      apply And.intro _ h5.left
      rewrite [Lemma_7_4_6]   --Goal : rel_prime m a ∧ rel_prime n a
      rewrite [congr_rel_prime h5.right.left,
        congr_rel_prime h5.right.right]
      show rel_prime m b ∧ rel_prime n c from
        And.intro h2.left.left h2.right.left
      done
    · -- Proof of mod_mod m n a = (b, c)
      rewrite [congr_iff_mod_eq, congr_iff_mod_eq] at h5
      rewrite [mod_mod_def, h5.right.left, h5.right.right]
        --Goal : (b % m, c % n) = (b, c)
      rewrite [Nat.mod_eq_of_lt h2.left.right,
        Nat.mod_eq_of_lt h2.right.right]
      rfl
      done
    done
  done

lemma Set_rp_below_prod {m n : Nat} (h1 : rel_prime m n) :
    Set_rp_below (m * n) ∼ (Set_rp_below m) ×ₛ (Set_rp_below n) :=
  equinum_image (mod_mod_one_one_on h1) (mod_mod_image h1)

/- Old version
def rp_mod_mod (m n a : Nat) (p : Nat × Nat) : Prop :=
  rel_prime (m * n) a ∧ a < m * n ∧ p.1 = a % m ∧ p.2 = a % n

lemma rp_mod_mod_def (m n a b c : Nat) :
    rp_mod_mod m n a (b, c) ↔
      rel_prime (m * n) a ∧ a < m * n ∧ b = a % m ∧ c = a % n := by rfl

lemma rp_mod_mod_rel_within {m n : Nat} (h1 : rel_prime m n) :
    rel_within (rp_mod_mod m n) (Set_rp_below (m * n))
      (Set_prod (Set_rp_below m) (Set_rp_below n)) := by
  define
  fix a; fix (b, c)
  assume h2
  rewrite [rp_mod_mod_def] at h2
  have h3 : m * n ≠ 0 := by linarith
  have h4 := left_ne_zero_of_mul h3
  have h5 := right_ne_zero_of_mul h3
  rewrite [←neZero_iff] at h4
  rewrite [←neZero_iff] at h5
  apply And.intro
  · -- Proof that a ∈ Set_rp_below
    define
    exact And.intro h2.left h2.right.left
    done
  · -- Proof that (b, c) ∈ Set_prod
    define
    rewrite [Lemma_7_4_6] at h2
    rewrite [h2.right.right.left, h2.right.right.right]
    apply And.intro
    · -- Proof that b ∈ Set_rp_below
      exact mod_elt_Set_rp_below h2.left.left
      done
    · -- Proof that c ∈ Set_rp_below
      exact mod_elt_Set_rp_below h2.left.right
      done
    done
  done

lemma rp_mod_mod_fcnl {m n : Nat} (h1 : rel_prime m n) :
    fcnl_on (rp_mod_mod m n) (Set_rp_below (m * n)) := by
  define
  fix a
  assume h2
  define at h2
  exists_unique
  · -- Existence
    apply Exists.intro (a % m, a % n)
    rewrite [rp_mod_mod_def]
    apply And.intro h2.left
    apply And.intro h2.right
    apply And.intro
    rfl
    rfl
    done
  · -- Uniqueness
    fix (b1, c1); fix (b2, c2)
    assume h3; assume h4
    rewrite [rp_mod_mod_def] at h3
    rewrite [rp_mod_mod_def] at h4
    rewrite [h3.right.right.left, h3.right.right.right,
      h4.right.right.left, h4.right.right.right]
    rfl
    done
  done

lemma rp_mod_mod_inv_fcnl {m n : Nat} (h1 : rel_prime m n) :
    fcnl_on (invRel (rp_mod_mod m n)) (Set_prod (Set_rp_below m) (Set_rp_below n)) := by
  define
  fix (b, c)
  assume h2
  rewrite [Set_prod_def, Set_rp_below_def, Set_rp_below_def] at h2
  have h3 : m ≠ 0 := by linarith
  have h4 : n ≠ 0 := by linarith
  rewrite [←neZero_iff] at h3
  rewrite [←neZero_iff] at h4
  exists_unique
  · -- Existence
    obtain r h5 from Lemma_7_4_7 h1 b c
    apply Exists.intro r
    rewrite [invRel_def, rp_mod_mod_def]
    apply And.intro
    · -- Proof of rel_prime (m * n) r
      rewrite [Lemma_7_4_6]
      rewrite [congr_rel_prime h5.right.left, congr_rel_prime h5.right.right]
      exact And.intro h2.left.left h2.right.left
      done
    · -- Proof of r < m * n ∧ b = r % m ∧ c = r % n
      apply And.intro h5.left
      rewrite [congr_iff_mod_eq, congr_iff_mod_eq] at h5
      rewrite [h5.right.left, h5.right.right]
      rewrite [Nat.mod_eq_of_lt h2.left.right, Nat.mod_eq_of_lt h2.right.right]
      apply And.intro
      rfl
      rfl
      done
    done
  · -- Uniqueness
    fix a1; fix a2
    assume h5; assume h6
    rewrite [invRel_def, rp_mod_mod_def] at h5
    rewrite [invRel_def, rp_mod_mod_def] at h6
    have h7 : b = a2 % m ∧ c = a2 % n := h6.right.right
    rewrite [h5.right.right.left, h5.right.right.right] at h7
    rewrite [←congr_iff_mod_eq, ←congr_iff_mod_eq] at h7
    rewrite [←Lemma_7_4_5 _ _ h1] at h7
    rewrite [congr_iff_mod_eq] at h7
    rewrite [Nat.mod_eq_of_lt h5.right.left, Nat.mod_eq_of_lt h6.right.left] at h7
    exact h7
    done
  done

lemma Set_rp_below_prod {m n : Nat} (h1 : rel_prime m n) :
    equinum (Set_rp_below (m * n)) (Set_prod (Set_rp_below m) (Set_rp_below n)) := by
  define
  apply Exists.intro (rp_mod_mod m n)
  define
  apply And.intro (rp_mod_mod_rel_within h1)
  exact And.intro (rp_mod_mod_fcnl h1) (rp_mod_mod_inv_fcnl h1)
  done
-/

--Used for phi multiplicative


/- Previous version
--8_1_6b used for phi multiplicative
lemma I_not_equinum_of_lt : ∀ ⦃n m : Nat⦄, n < m → ¬I n ∼ I m := by
  by_induc
  · -- Base Case
    fix m
    assume h1
    by_contra h2
    rewrite [←numElts_def, zero_elts_iff_empty] at h2
    define at h2
    contradict h2
    apply Exists.intro 0
    define
    exact h1
    done
  · -- Induction Step
    fix n
    assume ih
    fix m
    assume h1
    by_contra h2
    have h3 : m ≠ 0 := by linarith
    obtain k h4 from exists_eq_add_one_of_ne_zero h3
    rewrite [h4] at h2
    have h5 : n < k := by linarith
    have h6 : n ∈ I (n + 1) := I_max n
    have h7 : k ∈ I (k + 1) := I_max k
    have h8 := remove_one_equinum h2 h6 h7
    rewrite [I_diff, I_diff] at h8
    exact (ih h5) h8
    done
  done

theorem eq_of_I_equinum {n m : Nat} (h1 : I n ∼ I m) : n = m := by
  by_cases h2 : n < m
  · -- Case 1. h2 : n < m
    contradict h1 with h3
    exact I_not_equinum_of_lt h2
    done
  · -- Case 2. h2 ¬n < m
    by_cases h3 : m < n
    · -- Case 2.1. h3 : m < n
      have h4 := Theorem_8_1_3_2 h1
      contradict h4 with h5
      exact I_not_equinum_of_lt h3
      done
    · -- Case 2.2. h3 : ¬m < n
      linarith
      done
    done
  done

theorem numElts_unique {A : Type} {X : Set A} {m n : Nat}
    (h1 : numElts X m) (h2 : numElts X n) : m = n := by
  rewrite [numElts_def] at h1
  rewrite [numElts_def] at h2
  have h3 := Theorem_8_1_3_2 h2
  have h4 := Theorem_8_1_3_3 h1 h3
  exact eq_of_I_equinum h4
  done
-/

lemma eq_numElts_of_equinum {A B : Type} {X : Set A} {Y : Set B} {n : Nat}
    (h1 : X ∼ Y) (h2 : numElts X n) : numElts Y n := by
  rewrite [numElts_def] at h2   --h2 : I n ∼ X
  rewrite [numElts_def]         --Goal : I n ∼ Y
  show I n ∼ Y from Theorem_8_1_3_3 h2 h1
  done

theorem Theorem_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    phi (m * n) = (phi m) * (phi n) := by
  have h2 : numElts (Set_rp_below m) (phi m) := phi_is_numElts m
  have h3 : numElts (Set_rp_below n) (phi n) := phi_is_numElts n
  have h4 : numElts (Set_rp_below (m * n)) (phi (m * n)) :=
    phi_is_numElts (m * n)
  have h5 : numElts (Set_rp_below m ×ₛ Set_rp_below n) (phi (m * n)) :=
    eq_numElts_of_equinum (Set_rp_below_prod h1) h4
  have h6 : numElts (Set_rp_below m ×ₛ Set_rp_below n) (phi m * phi n) :=
    numElts_prod h2 h3
  show phi (m * n) = phi m * phi n from numElts_unique h5 h6
  done

/- Section 8.2 -/
--From exercises of Section 8.1
theorem Exercise_8_1_17 {A : Type} {X Y : Set A}
    (h1 : X ⊆ Y) (h2 : ctble Y) : ctble X := sorry

theorem Theorem_8_2_1_1 {A B : Type} {X : Set A} {Y : Set B}
    (h1 : ctble X) (h2 : ctble Y) : ctble (X ×ₛ Y) := by
  rewrite [ctble_iff_equinum_set_nat] at h1
  rewrite [ctble_iff_equinum_set_nat] at h2
  obtain (I : Set Nat) (h3 : I ∼ X) from h1
  obtain (J : Set Nat) (h4 : J ∼ Y) from h2
  have h5 : I ×ₛ J ∼ X ×ₛ Y := Theorem_8_1_2_1 h3 h4
  have h6 : I ×ₛ J ⊆ Univ (Nat × Nat) := by
    fix p : Nat × Nat
    assume h6 : p ∈ I ×ₛ J
    show p ∈ Univ (Nat × Nat) from elt_Univ p
    done
  have h7 : ctble (Univ (Nat × Nat)) := by
    define       --Goal : finite (Univ (ℕ × ℕ)) ∨ denum (Univ (ℕ × ℕ))
    apply Or.inr
    rewrite [denum_def]
    show Univ Nat ∼ Univ (Nat × Nat) from Theorem_8_1_3_2 NxN_equinum_N
    done
  have h8 : ctble (I ×ₛ J) := Exercise_8_1_17 h6 h7
  show ctble (X ×ₛ Y) from ctble_of_equinum_ctble h5 h8
  done

def enum_union_fam {A : Type}
  (F : Set (Set A)) (f : Set A → Rel Nat A) (R : Rel Nat (Set A))
  (n : Nat) (a : A) : Prop := ∃ (p : Nat × Nat), fnnn p = n ∧
    ∃ (X : Set A), X ∈ F ∧ R p.fst X ∧ (f X) p.snd a

lemma Lemma_8_2_2_1 {A : Type} {F : Set (Set A)} {f : Set A → Rel Nat A}
    (h1 : ctble F) (h2 : ∀ X ∈ F, fcnl_onto_from_nat (f X) X) :
    ctble (⋃₀ F) := by
  rewrite [Theorem_8_1_5_2] at h1
  rewrite [Theorem_8_1_5_2]
  obtain (R : Rel Nat (Set A)) (h3 : fcnl_onto_from_nat R F) from h1
  define at h3
  have Runiqueval : unique_val_on_N R := h3.left
  have Ronto : nat_rel_onto R F := h3.right
  set S : Rel Nat A := enum_union_fam F f R
  apply Exists.intro S
  define
  apply And.intro
  · -- Proof of unique_val_on_N S
    define
    fix n : Nat; fix a1 : A; fix a2 : A
    assume Sna1 : S n a1
    assume Sna2 : S n a2         --Goal : a1 = a2
    define at Sna1; define at Sna2
    obtain ((i1, j1) : Nat × Nat) (h4 : fnnn (i1, j1) = n ∧
      ∃ (X : Set A), X ∈ F ∧ R i1 X ∧ f X j1 a1) from Sna1
    obtain (X1 : Set A) (Xija1 : X1 ∈ F ∧ R i1 X1 ∧ f X1 j1 a1)
      from h4.right
    obtain ((i2, j2) : Nat × Nat) (h5 : fnnn (i2, j2) = n ∧
      ∃ (X : Set A), X ∈ F ∧ R i2 X ∧ f X j2 a2) from Sna2
    obtain (X2 : Set A) (Xija2 : X2 ∈ F ∧ R i2 X2 ∧ f X2 j2 a2)
      from h5.right
    rewrite [←h5.left] at h4
    have h6 : (i1, j1) = (i2, j2) :=
      fnnn_one_one (i1, j1) (i2, j2) h4.left
    have h7 : i1 = i2 ∧ j1 = j2 := Prod.mk.inj h6
    rewrite [h7.left, h7.right] at Xija1
      --Xija1 : X1 ∈ F ∧ R i2 X1 ∧ f X1 j2 a1
    define at Runiqueval
    have h8 : X1 = X2 := Runiqueval Xija1.right.left Xija2.right.left
    rewrite [h8] at Xija1       --Xija1 : X2 ∈ F ∧ R i2 X2 ∧ f X2 j2 a1
    have fX2fcnlonto : fcnl_onto_from_nat (f X2) X2 := h2 X2 Xija2.left
    define at fX2fcnlonto
    have fX2uniqueval : unique_val_on_N (f X2) := fX2fcnlonto.left
    define at fX2uniqueval
    show a1 = a2 from fX2uniqueval Xija1.right.right Xija2.right.right
    done
  · -- Proof of nat_rel_onto S (⋃₀ F)
    define
    fix x : A
    assume h4 : x ∈ ⋃₀ F    --Goal : ∃ (n : Nat), S n x
    define at h4
    obtain (X : Set A) (h5 : X ∈ F ∧ x ∈ X) from h4
    define at Ronto
    obtain (i : Nat) (h6 : R i X) from Ronto h5.left
    have fXfcnlonto : fcnl_onto_from_nat (f X) X := h2 X h5.left
    define at fXfcnlonto
    have fXonto : nat_rel_onto (f X) X := fXfcnlonto.right
    define at fXonto
    obtain (j : Nat) (h7 : f X j x) from fXonto h5.right
    apply Exists.intro (fnnn (i, j))
    define    --Goal : ∃ (p : Nat × Nat), fnnn p = fnnn (i, j) ∧
              --       ∃ (X : Set A), X ∈ F ∧ R p.fst X ∧ f X p.snd x
    apply Exists.intro (i, j)
    apply And.intro
    · -- Proof that fnnn (i, j) = fnnn (i, j)
      rfl
      done
    · -- Proof that ∃ (X : Set A), X ∈ F ∧
      --            R (i, j).fst X ∧ f X (i, j).snd x
      apply Exists.intro X
      show X ∈ F ∧ R (i, j).fst X ∧ f X (i, j).snd x from
        And.intro h5.left (And.intro h6 h7)
      done
    done
  done

/- Old version
def enum_union_fam {A : Type}
  (F : Set (Set A)) (f : Set A → Rel Nat A) (R : Rel Nat (Set A))
  (n : Nat) (a : A) : Prop := ∃ (X : Set A), X ∈ F ∧
    ∃ (p : Nat × Nat), fnnn p = n ∧ R p.fst X ∧ (f X) p.snd a

lemma Lemma_8_2_2_1 {A : Type} {F : Set (Set A)} {f : Set A → Rel Nat A}
    (h1 : ctble F) (h2 : ∀ X ∈ F, fcnl_onto_from_nat (f X) X) :
    ctble (⋃₀ F) := by
  rewrite [Theorem_8_1_5_2] at h1
  rewrite [Theorem_8_1_5_2]
  obtain (R : Rel Nat (Set A)) (h3 : fcnl_onto_from_nat R F) from h1
  define at h3
  have Runiqueval : unique_val_on_N R := h3.left
  have Ronto : nat_rel_onto R F := h3.right
  set S : Rel Nat A := enum_union_fam F f R
  apply Exists.intro S
  define
  apply And.intro
  · -- Proof of unique_val_on_N S
    define
    fix n : Nat; fix a1 : A; fix a2 : A
    assume h6 : S n a1
    assume h7 : S n a2         --Goal : a1 = a2
    define at h6; define at h7
    obtain (X1 : Set A) (Sna1 : X1 ∈ F ∧ ∃ (p : Nat × Nat),
      fnnn p = n ∧ R p.fst X1 ∧ f X1 p.snd a1) from h6
    obtain ((i1, j1) : Nat × Nat)
      (n_to_a1 : fnnn (i1, j1) = n ∧ R i1 X1 ∧ f X1 j1 a1) from Sna1.right
    obtain (X2 : Set A) (Sna2 : X2 ∈ F ∧ ∃ (p : Nat × Nat),
      fnnn p = n ∧ R p.fst X2 ∧ f X2 p.snd a2) from h7
    obtain ((i2, j2) : Nat × Nat)
      (n_to_a2 : fnnn (i2, j2) = n ∧ R i2 X2 ∧ f X2 j2 a2) from Sna2.right
    rewrite [←n_to_a2.left] at n_to_a1
    have h8 : (i1, j1) = (i2, j2) :=
      fnnn_one_one (i1, j1) (i2, j2) n_to_a1.left
    have h9 : i1 = i2 ∧ j1 = j2 := Prod.mk.inj h8
    have ija1 : R i1 X1 ∧ f X1 j1 a1 := n_to_a1.right
    have ija2 : R i2 X2 ∧ f X2 j2 a2 := n_to_a2.right
    rewrite [h9.left, h9.right] at ija1   --ija1 : R i2 X1 ∧ f X1 j2 a1
    define at Runiqueval
    have h10 : X1 = X2 := Runiqueval ija1.left ija2.left
    rewrite [h10] at ija1       --ija1 : R i2 X2 ∧ f X2 j2 a1
    have fX2fcnlonto : fcnl_onto_from_nat (f X2) X2 := h2 X2 Sna2.left
    define at fX2fcnlonto
    have fX2uniqueval : unique_val_on_N (f X2) := fX2fcnlonto.left
    define at fX2uniqueval
    show a1 = a2 from fX2uniqueval ija1.right ija2.right
    done
  · -- Proof of nat_rel_onto S (⋃₀ F)
    define
    fix x : A
    assume h4 : x ∈ ⋃₀ F    --Goal : ∃ (n : Nat), S n x
    define at h4
    obtain (X : Set A) (h5 : X ∈ F ∧ x ∈ X) from h4
    define at Ronto
    obtain (i : Nat) (h6 : R i X) from Ronto h5.left
    have fXfcnlonto : fcnl_onto_from_nat (f X) X := h2 X h5.left
    define at fXfcnlonto
    have fXonto : nat_rel_onto (f X) X := fXfcnlonto.right
    define at fXonto
    obtain (j : Nat) (h7 : f X j x) from fXonto h5.right
    apply Exists.intro (fnnn (i, j))
    define    --Goal : ∃ (X : Set A), X ∈ F ∧ ∃ (p : ℕ × ℕ),
              --       fnnn p = fnnn (i, j) ∧ R p.fst X ∧ f X p.snd x
    apply Exists.intro X
    apply And.intro h5.left
    apply Exists.intro (i, j)  --Goal : fnnn (i, j) = fnnn (i, j) ∧
                               --       R (i, j).fst X ∧ f X (i, j).snd x
    apply And.intro _ (And.intro h6 h7)
    rfl
    done
  done
-/

lemma Lemma_8_2_2_2 {A : Type} {F : Set (Set A)} (h : ∀ X ∈ F, ctble X) :
    ∃ (f : Set A → Rel Nat A), ∀ X ∈ F, fcnl_onto_from_nat (f X) X := by
  have h1 : ∀ (X : Set A), ∃ (SX : Rel Nat A),
      X ∈ F → fcnl_onto_from_nat SX X := by
    fix X
    by_cases h2 : X ∈ F
    · -- Case 1. h2 : X ∈ F
      have h3 : ctble X := h X h2
      rewrite [Theorem_8_1_5_2] at h3
      obtain (SX : Rel Nat A) (h4 : fcnl_onto_from_nat SX X) from h3
      apply Exists.intro SX
      assume h5 : X ∈ F
      show fcnl_onto_from_nat SX X from h4
      done
    · -- Case 2. h2 : X ∉ F
      apply Exists.intro (emptyRel Nat A)
      assume h3 : X ∈ F
      show fcnl_onto_from_nat (emptyRel Nat A) X from absurd h3 h2
      done
    done
  set f : Set A → Rel Nat A := fun (X : Set A) => Classical.choose (h1 X)
  apply Exists.intro f
  fix X : Set A
  show X ∈ F → fcnl_onto_from_nat (f X) X from Classical.choose_spec (h1 X)
  done

theorem Theorem_8_2_2 {A : Type} {F : Set (Set A)}
    (h1 : ctble F) (h2 : ∀ X ∈ F, ctble X) : ctble (⋃₀ F) := by
  obtain (f : Set A → Rel Nat A) (h3 : ∀ (X : Set A), X ∈ F →
    fcnl_onto_from_nat (f X) X) from Lemma_8_2_2_2 h2
  show ctble (⋃₀ F) from Lemma_8_2_2_1 h1 h3
  done

theorem func_from_graph_rtl {A B : Type} (F : Set (A × B)) :
    is_func_graph F → (∃ (f : A → B), graph f = F) := by
  assume h1 : is_func_graph F
  define at h1    --h1 : ∀ (x : A), ∃! (y : B), (x, y) ∈ F
  have h2 : ∀ (x : A), ∃ (y : B), (x, y) ∈ F := by
    fix x : A
    obtain (y : B) (h3 : (x, y) ∈ F)
      (h4 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show ∃ (y : B), (x, y) ∈ F from Exists.intro y h3
    done
  set f : A → B := fun (x : A) => Classical.choose (h2 x)
  apply Exists.intro f
  apply Set.ext
  fix (x, y) : A × B
  have h3 : (x, f x) ∈ F := Classical.choose_spec (h2 x)
  apply Iff.intro
  · -- (→)
    assume h4 : (x, y) ∈ graph f
    define at h4        --h4 : f x = y
    rewrite [h4] at h3
    show (x, y) ∈ F from h3
    done
  · -- (←)
    assume h4 : (x, y) ∈ F
    define              --Goal : f x = y
    obtain (z : B) (h5 : (x, z) ∈ F)
      (h6 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show f x = y from h6 (f x) y h3 h4
    done
  done

/- Theorem 8.2.4 -/
def seq {A : Type} (X : Set A) : Set (List A) :=
  { l : List A | ∀ (x : A), x ∈ l → x ∈ X }

lemma seq_def {A : Type} (X : Set A) (l : List A) :
    l ∈ seq X ↔ ∀ (x : A), x ∈ l → x ∈ X := by rfl

def seq_by_length {A : Type} (X : Set A) (n : Nat) : Set (List A) :=
  { l : List A | l ∈ seq X ∧ l.length = n }

lemma sbl_base {A : Type} (X : Set A) : seq_by_length X 0 = {[]} := by
  apply Set.ext
  fix l : List A
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ seq_by_length X 0
    define at h1   --h1 : l ∈ seq X ∧ List.length l = 0
    rewrite [List.length_eq_zero] at h1
    define
    show l = [] from h1.right
    done
  · -- (←)
    assume h1 : l ∈ {[]}
    define at h1     --h1 : l = []
    define           --Goal : l ∈ seq X ∧ List.length l = 0
    apply And.intro _ (List.length_eq_zero.rtl h1)
    define           --Goal : ∀ (x : A), x ∈ l → x ∈ X
    fix a : A
    assume h2 : a ∈ l
    contradict h2 with h3
    rewrite [h1]
    show ¬a ∈ [] from List.not_mem_nil a
    done
  done

def seq_cons (A : Type) (p : A × (List A)) : List A := p.fst :: p.snd

lemma seq_cons_def {A : Type} (x : A) (l : List A) :
    seq_cons A (x, l) = x :: l := by rfl

lemma seq_cons_one_one (A : Type) : one_to_one (seq_cons A) := by
  fix (a1, l1) : A × List A; fix (a2, l2) : A × List A
  assume h1 : seq_cons A (a1, l1) = seq_cons A (a2, l2)
  rewrite [seq_cons_def, seq_cons_def] at h1  --h1 : a1 :: l1 = a2 :: l2
  rewrite [List.cons_eq_cons] at h1           --h1 : a1 = a2 ∧ l1 = l2
  rewrite [h1.left, h1.right]
  rfl
  done

lemma seq_cons_image {A : Type} (X : Set A) (n : Nat) :
    image (seq_cons A) (X ×ₛ (seq_by_length X n)) = seq_by_length X (n + 1) := by
  apply Set.ext
  fix l : List A
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ image (seq_cons A) (X ×ₛ (seq_by_length X n))
    define at h1
    obtain ((a, L) : A × List A)
      (h2 : (a, L) ∈ X ×ₛ seq_by_length X n ∧ seq_cons A (a, L) = l) from h1
    have h3 : (a, L) ∈ X ×ₛ seq_by_length X n := h2.left
    define at h3      --h3 : a ∈ X ∧ L ∈ seq_by_length X n
    have h4 : L ∈ seq_by_length X n := h3.right
    define at h4      --h4 : L ∈ seq X ∧ List.length L = n
    have h5 : seq_cons A (a, L) = l := h2.right
    rewrite [seq_cons_def] at h5   --h5 : a :: L = l
    rewrite [←h5]
    define
    apply And.intro
    · -- Proof that a :: L ∈ seq X
      define
      fix b : A
      assume h6 : b ∈ a :: L
      rewrite [List.mem_cons] at h6  --h6 : b = a ∨ b ∈ L
      by_cases on h6
      · -- Case 1. h6 : b = a
        rewrite [h6]
        show a ∈ X from h3.left
        done
      · -- Case 2. h6 : b ∈ L
        rewrite [seq_def] at h4
        show b ∈ X from h4.left b h6
        done
      done
    · -- Proof that List.length (a :: L) = n + 1
      rewrite [←h4.right]
      show List.length (a :: L) = List.length L + 1 from
        List.length_cons a L
      done
    done
  · -- (←)
    assume h1 : l ∈ seq_by_length X (n + 1)
    define at h1   --h1 : l ∈ seq X ∧ List.length l = n + 1
    define
    obtain (a : A) (h2 : ∃ (L : List A), l = a :: L ∧ List.length L = n)
      from exists_cons_of_length_eq_succ h1.right
    obtain (L : List A) (h3 : l = a :: L ∧ List.length L = n) from h2
    apply Exists.intro (a, L)
      --Goal : (a, L) ∈ X ×ₛ seq_by_length X n ∧ seq_cons A (a, L) = l
    rewrite [Set_prod_def, seq_cons_def]
      --Goal : (a ∈ X ∧ L ∈ seq_by_length X n) ∧ a :: L = l
    apply And.intro _ h3.left.symm
    have h4 : l ∈ seq X := h1.left
    rewrite [h3.left, seq_def] at h4
      --h4 : ∀ (x : A), x ∈ a :: L → x ∈ X
    apply And.intro (h4 a (List.mem_cons_self a L))
    define    --Goal : L ∈ seq X ∧ List.length L = n
    apply And.intro _ h3.right
    define    --Goal : ∀ (x : A), x ∈ L → x ∈ X
    fix b : A
    assume h5 : b ∈ L
    show b ∈ X from h4 b (List.mem_cons_of_mem a h5)
    done
  done

lemma Lemma_8_2_4_1 {A : Type} (X : Set A) (n : Nat) :
    X ×ₛ (seq_by_length X n) ∼ seq_by_length X (n + 1) :=
  equinum_image (one_one_on_of_one_one (seq_cons_one_one A)
    (X ×ₛ (seq_by_length X n))) (seq_cons_image X n)

lemma Lemma_8_2_4_2 {A : Type} {X : Set A} (h1 : ctble X) :
    ∀ (n : Nat), ctble (seq_by_length X n) := by
  by_induc
  · -- Base Case
    rewrite [sbl_base]   --Goal : ctble {[]}
    define
    apply Or.inl         --Goal : finite {[]}
    define
    apply Exists.intro 1 --Goal : I 1 ∼ {[]}
    show I 1 ∼ {[]} from singleton_one_elt ([] : List A)
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ctble (seq_by_length X n)
    have h2 : X ×ₛ (seq_by_length X n) ∼ seq_by_length X (n + 1) :=
      Lemma_8_2_4_1 X n
    have h3 : ctble (X ×ₛ (seq_by_length X n)) := Theorem_8_2_1_1 h1 ih
    show ctble (seq_by_length X (n + 1)) from ctble_of_equinum_ctble h2 h3
    done
  done

def sbl_set {A : Type} (X : Set A) : Set (Set (List A)) :=
  { S : Set (List A) | ∃ (n : Nat), S = seq_by_length X n }

lemma Lemma_8_2_4_3 {A : Type} (X : Set A) : seq X = ⋃₀ (sbl_set X) := by
  apply Set.ext
  fix l : List A
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ seq X
    --define at h1
    define
    apply Exists.intro (seq_by_length X l.length)
    apply And.intro
    · -- Proof of seq_by_length X (List.length l) ∈ sbl_set X
      define
      apply Exists.intro l.length
      rfl
      done
    · -- Proof of l ∈ seq_by_length X (List.length l)
      define
      apply And.intro h1
      rfl
      done
    done
  · -- (←)
    assume h1 : l ∈ ⋃₀ (sbl_set X)
    define at h1
    obtain (S : Set (List A)) (h2 :  S ∈ sbl_set X ∧ l ∈ S) from h1
    have h3 : S ∈ sbl_set X := h2.left
    define at h3
    obtain (n : Nat) (h4 : S = seq_by_length X n) from h3
    have h5 : l ∈ S := h2.right
    rewrite [h4] at h5
    define at h5
    show l ∈ seq X from h5.left
    done
  done

def enum_sbl_sets {A : Type} (X : Set A)
    (n : Nat) (S : Set (List A)) : Prop := S = seq_by_length X n

lemma Lemma_8_2_4_4 {A : Type} (X : Set A) : ctble (sbl_set X) := by
  rewrite [Theorem_8_1_5_2]
  set R : Rel Nat (Set (List A)) := enum_sbl_sets X
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of unique_val_on_N R
    define
    fix n : Nat; fix S1 : Set (List A); fix S2 : Set (List A)
    assume h1 : R n S1
    assume h2 : R n S2
    define at h1      --h1 : S1 = seq_by_length X n
    define at h2      --h2 : S2 = seq_by_length X n
    rewrite [←h2] at h1
    show S1 = S2 from h1
    done
  · -- Proof of nat_rel_onto R (sbl_set X)
    define
    fix S : Set (List A)
    assume h1 : S ∈ sbl_set X  --Goal : ∃ (n : Nat), R n S
    define at h1
    obtain (n : Nat) (h2 : S = seq_by_length X n) from h1
    apply Exists.intro n
    define
    show S = seq_by_length X n from h2
    done
  done

theorem Theorem_8_2_4 {A : Type} {X : Set A} (h1 : ctble X) : ctble (seq X) := by
  set F : Set (Set (List A)) := sbl_set X
  have h2 : ctble F := Lemma_8_2_4_4 X
  have h3 : ∀ (S : Set (List A)), S ∈ F → ctble S := by
    fix S : Set (List A)
    assume h3 : S ∈ F
    define at h3
    obtain (n : Nat) (h4 : S = seq_by_length X n) from h3
    rewrite [h4]
    show ctble (seq_by_length X n) from Lemma_8_2_4_2 h1 n
    done
  rewrite [Lemma_8_2_4_3 X]
  show ctble (⋃₀ sbl_set X) from Theorem_8_2_2 h2 h3
  done
