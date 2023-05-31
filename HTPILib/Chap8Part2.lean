import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Examples of bijections with N and Z -/
theorem Exercise_6_1_16a1 : ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

theorem Exercise_6_1_16a2 : ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := sorry

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
  define : fnz (2 * k)  --Goal :
    -- (if 2 ∣ 2 * k then ↑(2 * k / 2) else -↑((2 * k + 1) / 2)) = ↑k
  rewrite [if_pos h1]    --Goal : ↑(2 * k / 2) = ↑k
  have h2 : 0 < 2 := by linarith
  rewrite [Nat.mul_div_cancel_left k h2]
  rfl
  done

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := by
  have h1 : nat_odd (2 * k + 1) := by
    define
    apply Exists.intro k
    rfl
    done
  have h2 : ¬(nat_even (2 * k + 1) ∧ nat_odd (2 * k + 1)) :=
    Exercise_6_1_16a2 (2 * k + 1)
  demorgan at h2
  disj_syll h2 h1
  have h3 : ¬2 ∣ 2 * k + 1 := h2
  define : fnz (2 * k + 1)
  rewrite [if_neg h3]
  have h4 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  have h5 : 0 < 2 := by linarith
  rewrite [h4, Nat.mul_div_cancel_left (k + 1) h5]
  rfl
  done

lemma fzn_nat (k : Nat) : fzn ↑k = 2 * k := by
  have h1 : (↑k : Int) ≥ 0 := Nat.cast_nonneg k
  define : fzn ↑k  --Goal : 
    -- (if ↑k ≥ 0 then 2 * Int.toNat ↑k
    -- else 2 * Int.toNat (-↑k) - 1) = 2 * k
  rewrite [if_pos h1, Int.toNat_coe_nat]
  rfl
  done

lemma fzn_neg_succ_nat (k : Nat) : fzn (-↑(k + 1)) = 2 * k + 1 := by
  have h1 : ¬(-(↑(k + 1) : Int) ≥ 0) := by
    by_contra h1
    have h2 : k + 1 ≥ 1 := by linarith
    have h3 : (↑(k + 1) : Int) ≥ ↑(1 : Nat) := Nat.cast_le.rtl h2
    rewrite [Nat.cast_one] at h3
    linarith
    done
  define : fzn (-↑(k + 1))
  rewrite [if_neg h1, neg_neg, Int.toNat_coe_nat]
  show 2 * (k + 1) - 1 = 2 * k + 1 :=
    calc 2 * (k + 1) - 1
      _ = 2 * k + 1 + 1 - 1 := by ring
      _ = 2 * k + 1 := Nat.add_sub_cancel _ _
  done

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

lemma fnz_fzn : fnz ∘ fzn = id  := by
  apply funext
  fix a : Int
  rewrite [comp_def]
  by_cases h1 : 0 ≤ a
  · -- Case 1. h1 : 0 ≤ a
    obtain (k : Nat) (h2 : a = ↑k) from Int.eq_ofNat_of_zero_le h1
    rewrite [h2, fzn_nat, fnz_even]
    rfl
    done
  · -- Case 2. h1 : ¬0 ≤ a
    have h2 : 0 ≤ -a := by linarith
    obtain (j : Nat) (h3 : -a = ↑j) from Int.eq_ofNat_of_zero_le h2
    have h4 : j ≠ 0 := by linarith
    obtain (k : Nat) (h5 : j = k + 1) from exists_eq_add_one_of_ne_zero h4
    rewrite [h5] at h3
    have h6 : a = -↑(k + 1) := by linarith
    rewrite [h6, fzn_neg_succ_nat, fnz_odd]
    rfl
    done
  done

lemma fzn_one_one : one_to_one fzn := by
  have h : ∃ (g : Nat → Int), g ∘ fzn = id := Exists.intro fnz fnz_fzn
  show one_to_one fzn from Theorem_5_3_3_1 fzn h
  done

lemma fzn_onto : onto fzn := by
  have h : ∃ (g : Nat → Int), fzn ∘ g = id := Exists.intro fnz fzn_fnz
  show onto fzn from Theorem_5_3_3_2 fzn h
  done

lemma fnz_one_one : one_to_one fnz := by
  have h : ∃ (g : Int → Nat), g ∘ fnz = id := Exists.intro fzn fzn_fnz
  show one_to_one fnz from Theorem_5_3_3_1 fnz h
  done

lemma fnz_onto : onto fnz := by
  have h : ∃ (g : Int → Nat), fnz ∘ g = id := Exists.intro fzn fnz_fzn
  show onto fnz from Theorem_5_3_3_2 fnz h
  done


/- Bijection from Nat × Nat to Nat -/
-- triangular numbers
def tri (k : Nat) : Nat := k * (k + 1) / 2

def fnnn (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.1

lemma fnnn_def (a b : Nat) : fnnn (a, b) = tri (a + b) + a := by rfl

#eval [fnnn (0, 0), fnnn (0, 1), fnnn (1, 0), fnnn (0, 2), fnnn (1, 1)]
  --Answer: [0, 1, 2, 3, 4]

lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 :=
  calc tri (k + 1)
    _ = (k + 1) * (k + 1 + 1) / 2 := by rfl
    _ = (k * (k + 1) + 2 * (k + 1)) / 2 := by ring
    _ = k * (k + 1) / 2 + (k + 1) := Nat.add_mul_div_left _ _ two_pos
    _ = tri k + (k + 1) := by rfl
    _ = tri k + k + 1 := by ring

lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := by
  have h2 : j + 1 ≤ k + 1 := by linarith
  have h3 : j * (j + 1) ≤ k * (k + 1) :=
    calc j * (j + 1)
      _ ≤ k * (j + 1) := Nat.mul_le_mul_right _ h1
      _ ≤ k * (k + 1) := Nat.mul_le_mul_left _ h2
  show tri j ≤ tri k from Nat.div_le_div_right h3
  done

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
  define
  fix (a1, b1); fix (a2, b2)
  assume h1 : fnnn (a1, b1) = fnnn (a2, b2)
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

def RelWithinFromFunc {A B : Type} (f : A → B) (X : Set A)
  (x : A) (y : B) : Prop := x ∈ X ∧ f x = y

def one_one_on {A B : Type} (f : A → B) (X : Set A) : Prop :=
  ∀ ⦃x1 x2 : A⦄, x1 ∈ X → x2 ∈ X → f x1 = f x2 → x1 = x2

theorem equinum_image {A B : Type} {X : Set A} {f : A → B}
    (h1 : one_one_on f X) : X ∼ image f X := by
  define   --Goal : ∃ (R : Rel A B), matching R X (image f X)
  set R : Rel A B := RelWithinFromFunc f X
  apply Exists.intro R
  define   --Goal : rel_within R X (image f X) ∧
           --fcnl_on R X ∧ fcnl_on (invRel R) (image f X)
  apply And.intro
  · -- Proof of rel_within
    define --Goal : ∀ ⦃x : A⦄ ⦃y : B⦄, R x y → x ∈ X ∧ y ∈ image f X
    fix x : A; fix y : B
    assume h2 : R x y  --Goal : x ∈ X ∧ y ∈ image f X
    define at h2       --h2 : x ∈ X ∧ f x = y
    apply And.intro h2.left
    define
    show ∃ (x : A), x ∈ X ∧ f x = y from Exists.intro x h2
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R X
      define  --Goal : ∀ ⦃x : A⦄, x ∈ X → ∃! (y : B), R x y
      fix x : A
      assume h2 : x ∈ X
      exists_unique
      · -- Existence
        apply Exists.intro (f x)
        define  --Goal : x ∈ X ∧ f x = f x
        apply And.intro h2
        rfl
        done
      · -- Uniqueness
        fix y1 : B; fix y2 : B
        assume h3 : R x y1
        assume h4 : R x y2   --Goal : y1 = y2
        define at h3; define at h4
          --h3 : x ∈ X ∧ f x = y1;  h4 : x ∈ X ∧ f x = y2
        rewrite [h3.right] at h4
        show y1 = y2 from h4.right
        done
      done
    · -- Proof of fcnl_on (invRel R) (image f X)
      define
      fix y : B
      assume h2 : y ∈ image f X
      define at h2
      obtain (x : A) (h3 : x ∈ X ∧ f x = y) from h2
      exists_unique
      · -- Existence
        apply Exists.intro x
        define
        show x ∈ X ∧ f x = y from h3
        done
      · -- Uniqueness
        fix x1 : A; fix x2 : A
        assume h4 : invRel R y x1
        assume h5 : invRel R y x2
        define at h4; define at h5
        rewrite [←h5.right] at h4
        show x1 = x2 from h1 h4.left h5.left h4.right
        done
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

def Range {A B : Type} (f : A → B) : Set B := image f (Univ A)

theorem equinum_Range {A B : Type} {f : A → B} (h : one_to_one f) :
    Univ A ∼ Range f := equinum_image (one_one_on_of_one_one h (Univ A))

theorem equinum_Univ {A B : Type} {f : A → B}
    (h1 : one_to_one f) (h2 : onto f) : Univ A ∼ Univ B := by
  have h3 : Univ A ∼ Range f := equinum_Range h1
  have h4 : Range f = Univ B := by
    apply Set.ext
    fix b : B
    apply Iff.intro
    · -- (→)
      assume h4 : b ∈ Range f
      show b ∈ Univ B from elt_Univ b
      done
    · -- (←)
      assume h4 : b ∈ Univ B
      define at h2
      obtain (a : A) (h5 : f a = b) from h2 b
      apply Exists.intro a
      apply And.intro _ h5
      show a ∈ Univ A from elt_Univ a
      done
    done
  rewrite [h4] at h3
  show Univ A ∼ Univ B from h3
  done

theorem Z_equinum_N : Univ Int ∼ Univ Nat :=
  equinum_Univ fzn_one_one fzn_onto

theorem NxN_equinum_N : Univ (Nat × Nat) ∼ Univ Nat :=
  equinum_Univ fnnn_one_one fnnn_onto

/- Theorem 8.1.2 -/
def Set_prod {A B : Type} (X : Set A) (Y : Set B) : Set (A × B) :=
  { (a, b) : A × B | a ∈ X ∧ b ∈ Y }

notation:75 X:75 " ×ₛ " Y:75 => Set_prod X Y

lemma Set_prod_def {A B : Type} (X : Set A) (Y : Set B) (a : A) (b : B) :
    (a, b) ∈ X ×ₛ Y ↔ a ∈ X ∧ b ∈ Y := by rfl

def Rel_prod {A B C D : Type} (R : Rel A B) (S : Rel C D)
  (p : A × C) (q : B × D) : Prop := R p.1 q.1 ∧ S p.2 q.2

notation:75 R:75 " ×ᵣ " S:75 => Rel_prod R S

lemma Rel_prod_def {A B C D : Type} (R : Rel A B) (S : Rel C D)
    (a : A) (b : B) (c : C) (d : D) :
    (R ×ᵣ S) (a, c) (b, d) ↔ R a b ∧ S c d := by rfl

lemma prod_fcnl {A B C D : Type} {R : Rel A B} {S : Rel C D} {X : Set A} {Y : Set C}
    (h1 : fcnl_on R X) (h2 : fcnl_on S Y) : fcnl_on (R ×ᵣ S) (X ×ₛ Y) := by
  define
  --define at h1; define at h2
  fix (a, c)
  assume h3
  define at h3
  exists_unique
  · -- Existence
    obtain b h4 from fcnl_exists h1 h3.left
    obtain d h5 from fcnl_exists h2 h3.right
    apply Exists.intro (b, d)
    rewrite [Rel_prod_def]
    exact And.intro h4 h5
    done
  · -- Uniqueness
    fix (b1, d1); fix (b2, d2)
    assume h4; assume h5
    rewrite [Rel_prod_def] at h4
    rewrite [Rel_prod_def] at h5
    have h6 := fcnl_unique h1 h3.left h4.left h5.left
    have h7 := fcnl_unique h2 h3.right h4.right h5.right
    rewrite [h6, h7]
    rfl
    done
  done

lemma inv_Rel_prod {A B C D : Type} (R : Rel A B) (S : Rel C D) :
    invRel (R ×ᵣ S) = invRel R ×ᵣ invRel S := by rfl

lemma prod_match {A B C D : Type} {U : Set A} {V : Set B} {W : Set C} {X : Set D}
    {R : Rel A B} {S : Rel C D} (h1 : matching R U V) (h2 : matching S W X) :
    matching (R ×ᵣ S) (U ×ₛ W) (V ×ₛ X) := by
  define; define at h1; define at h2
  apply And.intro
  · -- Proof of rel_within
    define
    fix (a, c)
    fix (b, d)
    assume h3
    rewrite [Rel_prod_def] at h3
    rewrite [Set_prod_def, Set_prod_def]
    have h4 := h1.left h3.left
    have h5 := h2.left h3.right
    exact And.intro (And.intro h4.left h5.left) (And.intro h4.right h5.right)
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on
      exact prod_fcnl h1.right.left h2.right.left 
      done
    · -- Proof of fcnl_on inv
      rewrite [inv_Rel_prod]
      exact prod_fcnl h1.right.right h2.right.right
      done
    done
  done

theorem Theorem_8_1_2_1 {A B C D : Type} {U : Set A} {V : Set B} {W : Set C} {X : Set D}
    (h1 : U ∼ V) (h2 : W ∼ X) : U ×ₛ W ∼ V ×ₛ X := by
  define at h1; define at h2
  obtain R h3 from h1
  obtain S h4 from h2
  define
  apply Exists.intro (R ×ᵣ S)
  exact prod_match h3 h4
  done

def Rel_union {A B : Type} (R S : Rel A B) : Rel A B :=
  RelFromExt (extension R ∪ extension S)
--def Rel_union {A B : Type} (R S : Rel A B) (a : A) (b : B) : Prop :=
--  R a b ∨ S a b

notation:75 R:75 " ∪ᵣ " S:75 => Rel_union R S

lemma Rel_union_def {A B : Type} (R S : Rel A B) (a : A) (b : B) :
    (R ∪ᵣ S) a b ↔ R a b ∨ S a b := by rfl

lemma union_fcnl_left {A B : Type} {R S : Rel A B} {U W : Set A} {V X : Set B} {a : A}
    (h1 : empty (U ∩ W)) (h2 : matching R U V) (h3 : matching S W X)
    (h4 : a ∈ U) : ∃! (b : B), (R ∪ᵣ S) a b := by
  define at h2
  obtain b h5 from fcnl_exists h2.right.left h4
  exists_unique
  · -- Existence
    apply Exists.intro b
    rewrite [Rel_union_def]
    exact Or.inl h5
    done
  · -- Uniqueness
    fix b1; fix b2
    assume h6; assume h7
    rewrite [Rel_union_def] at h6; rewrite [Rel_union_def] at h7
    have h8 : ∀ (y : B), ¬S a y := by
      fix y
      contradict h1 with h9
      have h10 := match_rel_within h3 h9
      exact Exists.intro a (And.intro h4 h10.left)
      done
    disj_syll h6 (h8 b1)
    disj_syll h7 (h8 b2)
    exact fcnl_unique h2.right.left h4 h6 h7
    done
  done

lemma Rel_union_comm {A B : Type} (R S : Rel A B) :
    R ∪ᵣ S = S ∪ᵣ R :=
  calc R ∪ᵣ S
    _ = RelFromExt (extension R ∪ extension S) := by rfl
    _ = RelFromExt (extension S ∪ extension R) := by rw [union_comm]
    _ = S ∪ᵣ R := by rfl

lemma inter_comm {A : Type} (X Y : Set A) : X ∩ Y = Y ∩ X := by
  apply Set.ext
  fix x
  define : x ∈ X ∩ Y
  define : x ∈ Y ∩ X
  exact And.comm
  done

lemma inv_Rel_union {A B : Type} (R S : Rel A B) :
    invRel (R ∪ᵣ S) = invRel R ∪ᵣ invRel S := by rfl

lemma union_fcnl {A B : Type} {R S : Rel A B} {U W : Set A} {V X : Set B}
    (h1 : empty (U ∩ W)) (h2 : matching R U V) (h3 : matching S W X) :
    fcnl_on (R ∪ᵣ S) (U ∪ W) := by
  define
  fix a
  assume h4
  define at h4
  by_cases on h4
  · -- Case 1. h4 : a ∈ U
    exact union_fcnl_left h1 h2 h3 h4
    done
  · -- Case 2. h4 : a ∈ W
    rewrite [Rel_union_comm]
    rewrite [inter_comm] at h1
    exact union_fcnl_left h1 h3 h2 h4
    done
  done

lemma union_match {A B : Type} {U W : Set A} {V X : Set B} {R S : Rel A B}
    (h1 : empty (U ∩ W)) (h2 : empty (V ∩ X))
    (h3 : matching R U V) (h4 : matching S W X) :
    matching (R ∪ᵣ S) (U ∪ W) (V ∪ X) := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a; fix b
    assume h5
    rewrite [Rel_union_def] at h5
    by_cases on h5
    · -- Case 1. h7 : R a b
      have h6 := match_rel_within h3 h5
      exact And.intro (Or.inl h6.left) (Or.inl h6.right)
      done
    · -- Case 2. h7 : S a b
      have h6 := match_rel_within h4 h5
      exact And.intro (Or.inr h6.left) (Or.inr h6.right)
      done
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on
      exact union_fcnl h1 h3 h4
      done
    · -- Proof of fcnl_on inv
      rewrite [inv_Rel_union]
      have h5 := inv_match h3
      have h6 := inv_match h4
      exact union_fcnl h2 h5 h6
      done
    done
  done

theorem Theorem_8_1_2_2 {A B : Type} {U W : Set A} {V X : Set B}
    (h1 : empty (U ∩ W)) (h2 : empty (V ∩ X)) (h3 : U ∼ V) (h4 : W ∼ X) :
    U ∪ W ∼ V ∪ X := by
  define at h3; define at h4
  obtain R h5 from h3
  obtain S h6 from h4
  define
  apply Exists.intro (R ∪ᵣ S)
  exact union_match h1 h2 h5 h6
  done

/- Subsets of Nat are finite or denum. -/
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

lemma neb_unique (X : Set Nat) : ∀ ⦃n : Nat⦄, ∀ ⦃s1 s2 : Nat⦄,
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
      have h4 := ih h1.right h2.right
      show s1 = s2 from
        calc s1
          _ = s1 - 1 + 1 := (Nat.sub_add_cancel h1.left).symm
          _ = s2 - 1 + 1 := by rw [h4]
          _ = s2 := Nat.sub_add_cancel h2.left
      done
    · -- Case 2. h3 : n ∉ X
      rewrite [neb_step_not_elt h3] at h1
      rewrite [neb_step_not_elt h3] at h2
      exact ih h1 h2
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

lemma enum_not_lt {X : Set Nat} {t n1 n2 : Nat} (h1 : enum X t n1) (h2 : enum X t n2) : ¬n1 < n2 := by
  by_contra h3
  define at h2
  have h4 : n2 ≥ n1 + 1 := by linarith
  have h5 := neb_increase h1 h4 h2.right
  linarith
  done

lemma enum_unique (X : Set Nat) (t : Nat) :
    ∀ ⦃n1 n2 : Nat⦄, enum X t n1 → enum X t n2 → n1 = n2 := by
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
    exact neb_unique X h2.right h3.right
    done
  done

lemma bdd_subset_nat {X : Set Nat} {m s : Nat} (h1 : ∀ (n : Nat), n ∈ X → n < m)
    (h2 : num_elts_below X m s) : I s ∼ X := by
  define
  apply Exists.intro (enum X)
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

lemma unbdd_subset_nat {X : Set Nat} (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ X ∧ n ≥ m) :
    denum X := by
  define
  apply Exists.intro (enum X)
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
    done
  done

/- Theorem 8.1.5 -/
def unique_val_on_N {A : Type} (R : Rel Nat A) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃x1 x2 : A⦄, R n x1 → R n x2 → x1 = x2

def nat_rel_onto {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ X → ∃ (n : Nat), R n x

def fcnl_onto_from_nat {A : Type} (R : Rel Nat A) (X : Set A) : Prop :=
  unique_val_on_N R ∧ nat_rel_onto R X

lemma Lemma_8_1_5_12 {A : Type} {I : Set Nat} {X : Set A}
    (h1 : I ∼ X) : ∃ (R : Rel Nat A), fcnl_onto_from_nat R X := by
  define at h1
  obtain R h2 from h1
  define at h2
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of unique_val_on_N
    define
    fix n; fix x1; fix x2
    assume h3; assume h4
    have h5 := h2.left h3
    exact fcnl_unique h2.right.left h5.left h3 h4
    done
  · -- Proof of nat_rel_onto
    define
    fix x
    assume h3
    exact fcnl_exists h2.right.right h3
    done
  done

theorem Theorem_8_1_5_1_to_2 {A : Type} {X : Set A} (h1 : ctble X) :
    ∃ (R : Rel Nat A), fcnl_onto_from_nat R X := by
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

def fcnl_one_one_to_nat {A : Type} (R : Rel A Nat) (X : Set A) : Prop :=
  fcnl_on R X ∧ ∀ ⦃x1 x2 : A⦄ ⦃n : Nat⦄, x1 ∈ X → x2 ∈ X → R x1 n → R x2 n → x1 = x2

def least_witness {A : Type} (S : Rel A Nat) (x : A) (n : Nat) : Prop :=
  S x n ∧ ∀ (m : Nat), S x m → n ≤ m

theorem Theorem_8_1_5_2_to_3 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel Nat A), fcnl_onto_from_nat R X) :
    ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X := by
  obtain S h2 from h1
  define at h2
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
      obtain p h5 from h4 h3
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
    exact h7 h5.left h6.left
    done
  done

def restrict_to {A B : Type} (S : Rel A B) (X : Set A) (x : A) (y : B) : Prop :=
  x ∈ X ∧ S x y

theorem Theorem_8_1_5_3_to_1 {A : Type} {X : Set A}
    (h1 : ∃ (R : Rel A Nat), fcnl_one_one_to_nat R X) :
    ctble X := by
  obtain S h2 from h1
  define at h2
  set Y : Set Nat := { n : Nat | ∃ x ∈ X, S x n }
  have h3 : X ∼ Y := by
    set R : Rel A Nat := restrict_to S X
    define
    apply Exists.intro R
    define
    apply And.intro
    · -- Proof of rel_within R X Y
      define
      fix x; fix n
      assume h3
      define at h3
      apply And.intro h3.left
      define
      exact Exists.intro x h3
      done
    · --
      apply And.intro
      · -- Proof of fcnl_on R X
        define
        fix x
        assume h3
        exists_unique
        · -- Existence
          obtain y h4 from fcnl_exists h2.left h3
          apply Exists.intro y
          define
          exact And.intro h3 h4
          done
        · -- Uniqueness
          fix y1; fix y2
          assume h4; assume h5
          define at h4; define at h5
          exact fcnl_unique h2.left h3 h4.right h5.right
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
          exact h2.right h5.left h6.left h5.right h6.right
          done
        done
      done
    done
  have h4 : Y ∼ X := Theorem_8_1_3_2 h3
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
    ctble X ↔ ∃ (R : Rel Nat A), fcnl_onto_from_nat R X := by
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

/- Theorem 8.1.6: Q is denumerable -/
def fqn (q : Rat) : Nat := fnnn (fzn q.num, q.den)

lemma fqn_def (q : Rat) : fqn q = fnnn (fzn q.num, q.den) := by rfl

lemma fqn_one_one : one_to_one fqn := by
  define
  fix q1; fix q2
  assume h1
  rewrite [fqn_def, fqn_def] at h1
  have h2 := fnnn_one_one _ _ h1
  have h3 := Prod.mk.inj h2
  have h4 := fzn_one_one _ _ h3.left
  exact Rat.ext q1 q2 h4 h3.right
  done

/- Old versions
def Range {A B : Type} (f : A → B) : Set B := Ran (graph f)
--def Range {A B : Type} (f : A → B) : Set B := { y : B | ∃ (x : A), f x = y }

lemma Range_def {A B : Type} (f : A → B) (y : B) :
    y ∈ Range f ↔ ∃ (x : A), f x = y := by rfl

def RelFromFunc {A B : Type} (f : A → B) : Rel A B := RelFromExt (graph f)
--def RelFromFunc {A B : Type} (f : A → B) (a : A) (b : B) : Prop := f a = b

theorem equinum_Range {A B : Type} {f : A → B} (h1 : one_to_one f) : equinum (Univ A) (Range f) := by
  define
  set R : Rel A B := RelFromFunc f
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a; fix b
    assume h2
    apply And.intro (elt_Univ a)
    rewrite [Range_def]
    define at h2
    exact Exists.intro a h2
    done
  · --
    apply And.intro
    · -- Proof of fcnl_on R
      define
      fix a
      assume h2
      exists_unique
      · -- Existence
        apply Exists.intro (f a)
        define
        rfl
        done
      · -- Uniqueness
        fix b1; fix b2
        assume h3; assume h4
        define at h3; define at h4
        rewrite [h3] at h4
        exact h4
        done
      done
    · -- Proof of fcnl_on (invRel R)
      define
      fix b
      assume h2
      rewrite [Range_def] at h2
      obtain a h3 from h2
      exists_unique
      · -- Existence
        apply Exists.intro a
        define
        exact h3
        done
      · -- Uniqueness
        fix a1; fix a2
        assume h4; assume h5
        define at h4; define at h5
        rewrite [←h5] at h4
        exact h1 a1 a2 h4
        done
      done
    done
  done
-/
lemma Q_equinum_Range_fqn : Univ Rat ∼ Range fqn := equinum_Range fqn_one_one

lemma fqn_Nat (m : Nat) : fqn ↑m = fnnn (fzn m, 1) := by rfl

lemma Range_fqn_unbdd : ∀ (m : Nat), ∃ (n : Nat), n ∈ Range fqn ∧ n ≥ m := by
  fix m
  set n : Nat := fqn ↑m
  have h1 : n = fnnn (fzn m, 1) := by rfl
  rewrite [fzn_nat, fnnn_def] at h1
  apply Exists.intro n
  apply And.intro
  · -- Proof that n ∈ Range fqn
    define
    apply Exists.intro ↑m
    apply And.intro (elt_Univ (↑m : Rat))
    rfl
    done
  · -- Proof that n ≥ m
    exact
      calc n
        _ = tri (2 * m + 1) + 2 * m := h1
        _ ≥ m := by linarith
    done
  done

theorem Q_denum : denum (Univ Rat) := by
  have h1 : Univ Nat ∼ Range fqn := unbdd_subset_nat Range_fqn_unbdd
  have h2 : Univ Rat ∼ Range fqn := Q_equinum_Range_fqn
  have h3 : Range fqn ∼ Univ Rat := Theorem_8_1_3_2 h2
  exact Theorem_8_1_3_3 h1 h3
  done

/- More on finite sets -/
lemma eq_numElts_of_equinum {A B : Type} {X : Set A} {Y : Set B} {n : Nat}
    (h1 : X ∼ Y) (h2 : numElts X n) : numElts Y n := by
  rewrite [numElts_def] at h2
  rewrite [numElts_def]
  exact Theorem_8_1_3_3 h2 h1
  done

lemma I_not_equinum_of_lt : ∀ ⦃n m : Nat⦄, n < m → ¬I n ∼ I m := by
  by_induc
  · -- Base Case
    fix m
    assume h1
    by_contra h2
    have h3 : numElts (I m) 0 := h2
    rewrite [zero_elts_iff_empty] at h3
    define at h3
    contradict h3
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

theorem Exercise_8_1_6a {n m : Nat} (h1 : I n ∼ I m) : n = m := by
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

theorem Exercise_8_1_6b {A : Type} {X : Set A} {m n : Nat}
    (h1 : numElts X m) (h2 : numElts X n) : m = n := by
  rewrite [numElts_def] at h1
  rewrite [numElts_def] at h2
  have h3 := Theorem_8_1_3_2 h2
  have h4 := Theorem_8_1_3_3 h1 h3
  exact Exercise_8_1_6a h4
  done

def shift (m n : Nat) : Nat := m + n

lemma shift_def (m n : Nat) : shift m n = m + n := by rfl

lemma shift_one_one (m : Nat) : one_to_one (shift m) := by
  define
  fix n1; fix n2
  assume h1
  rewrite [shift_def, shift_def] at h1
  exact Nat.add_left_cancel h1
  done

lemma shift_I_equinum (m n : Nat) : I (m + n) \ I m ∼ I n := by
  have h1 : one_one_on (shift m) (I n) := one_one_on_of_one_one (shift_one_one m) (I n)
  have h2 := equinum_image h1
  have h3 : image (shift m) (I n) = I (m + n) \ I m := by
    apply Set.ext
    fix k
    apply Iff.intro
    · -- (→)
      assume h3
      define at h3
      obtain j h4 from h3
      rewrite [I_def, shift_def] at h4
      define
      apply And.intro
      · -- Proof that k ∈ I (m + n)
        define
        linarith
        done
      · -- Proof that ¬k ∈ I m
        define
        linarith
        done
      done
    · -- (←)
      assume h3
      define at h3
      rewrite [I_def, I_def] at h3
      have h4 : m ≤ k := by linarith
      define
      obtain j h5 from Nat.exists_eq_add_of_le h4
      apply Exists.intro j
      rewrite [I_def, shift_def]
      apply And.intro _ h5.symm
      linarith
      done
    done
  rewrite [h3] at h2
  exact Theorem_8_1_3_2 h2
  done

/- Old proof
  define
  set R : Rel Nat Nat := fun (a b : Nat) => b < n ∧ a = m + b
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix a; fix b
    assume h1
    define at h1
    apply And.intro
    · -- Proof that a ∈ I (m + n) \ I m
      define
      apply And.intro
      · -- Proof that a ∈ I (m + n)
        define
        linarith
        done
      · -- Proof that a ∉ I m
        define
        linarith
        done
      done
    · -- Proof that b ∈ I n
      define
      exact h1.left
      done
    done
  · -- Proof of fcnls_ons
    apply And.intro
    · -- Proof of fcnl_on R (I (m + n) \ I n)
      define
      fix j
      assume h1
      define at h1
      have h2 := h1.left
      have h3 := h1.right
      define at h2; define at h3
      have h4 : m ≤ j := by linarith
      exists_unique
      · -- Existence
        obtain a h5 from Nat.exists_eq_add_of_le h4
        apply Exists.intro a
        define
        apply And.intro _ h5
        linarith
        done
      · -- Uniqueness
        fix k1; fix k2
        assume h5; assume h6
        define at h5; define at h6
        rewrite [h5.right] at h6
        exact Nat.add_left_cancel h6.right
        done
      done
    · -- Proof of fcnl_on (invRel R) (I n)
      define
      fix k
      assume h1
      define at h1
      exists_unique
      · -- Existence
        apply Exists.intro (m + k)
        define
        apply And.intro h1
        rfl
        done
      · -- Uniqueness
        fix j1; fix j2
        assume h2; assume h3
        define at h2; define at h3
        rewrite [←h3.right] at h2
        exact h2.right
        done
      done 
    done
  done
-/

lemma inter_diff_empty {A : Type} (X Y : Set A) : empty (X ∩ (Y \ X)) := by
  define
  by_contra h1
  obtain x h2 from h1
  define at h2
  have h3 := h2.right
  define at h3
  exact h3.right h2.left
  done

lemma union_diff {A : Type} {X Y : Set A} (h : X ⊆ Y) : X ∪ (Y \ X) = Y := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- (→)
    assume h1
    define at h1
    by_cases on h1
    · -- Case 1. x ∈ X
      exact h h1
      done
    · -- Case 2. x ∈ Y \ X
      define at h1
      exact h1.left
      done
    done
  · -- (←)
    assume h1
    define
    or_right with h2
    define
    exact And.intro h1 h2
    done
  done

lemma I_incr {m n : Nat} (h : m ≤ n) : I m ⊆ I n := by
  fix x
  assume h1
  define at h1; define
  linarith
  done

theorem Theorem_8_1_7 {A : Type} {X Y : Set A} {m n : Nat} (h1 : empty (X ∩ Y))
    (h2 : numElts X m) (h3 : numElts Y n) : numElts (X ∪ Y) (m + n) := by
  rewrite [numElts_def]
  rewrite [numElts_def] at h2
  rewrite [numElts_def] at h3
  have h4 : empty (I m ∩ (I (m + n) \ I m)) := inter_diff_empty (I m) (I (m + n))
  have h5 : I (m + n) \ I m ∼ I n := shift_I_equinum m n
  have h6 := Theorem_8_1_3_3 h5 h3
  have h7 := Theorem_8_1_2_2 h4 h1 h2 h6
  have h8 : m ≤ m + n := by linarith
  have h9 : I m ⊆ I (m + n) := I_incr h8
  rewrite [union_diff h9] at h7
  exact h7
  done

def pair_with_const (A : Type) {B : Type} (b : B) (x : A) : A × B := (x, b)

lemma pwc_def {A B : Type} (b : B) (x : A) : pair_with_const A b x = (x, b) := by rfl

lemma pwc_one_one (A : Type) {B : Type} (b : B) : one_to_one (pair_with_const A b) := by
  define
  fix x1; fix x2
  assume h1
  rewrite [pwc_def, pwc_def] at h1
  exact (Prod.mk.inj h1).left
  done

lemma prod_singleton_numElts {A B : Type} {X : Set A} {n : Nat}
    (h1 : numElts X n) (b : B) : numElts (X ×ₛ {b}) n := by
  rewrite [numElts_def] at h1
  rewrite [numElts_def]
  have h2 := one_one_on_of_one_one (pwc_one_one A b) X
  have h3 := equinum_image h2
  have h4 : image (pair_with_const A b) X = X ×ₛ {b} := by
    apply Set.ext
    fix (x, y)
    apply Iff.intro
    · -- (→)
      assume h4
      define at h4
      obtain x' h5 from h4
      rewrite [pwc_def] at h5
      rewrite [←h5.right]
      define
      apply And.intro h5.left
      define
      rfl
      done
    · -- (←)
      assume h4
      define at h4
      define : y ∈ {b} at h4
      define
      apply Exists.intro x
      apply And.intro h4.left
      rewrite [pwc_def, h4.right]
      rfl
      done
    done
  rewrite [h4] at h3
  exact Theorem_8_1_3_3 h1 h3
  done

/- Old version
def pair_with_const {A B : Type} (X : Set A) (b : B) (x : A) (p : A × B) : Prop :=
  x ∈ X ∧ p.1 = x ∧ p.2 = b

lemma pair_with_const_def {A B : Type} (X : Set A) (b : B) (x x' : A) (y : B) :
    pair_with_const X b x (x', y) ↔ x ∈ X ∧ x' = x ∧ y = b := by rfl

lemma prod_singleton_numElts {A B : Type} {X : Set A} {n : Nat} (h1 : numElts X n) (b : B) :
    numElts (Set_prod X {b}) n := by
  rewrite [numElts_def] at h1
  rewrite [numElts_def]
  have h2 : equinum X (Set_prod X {b}) := by
    define
    apply Exists.intro (pair_with_const X b)
    define
    apply And.intro
    · -- Proof of rel_within
      define
      fix x
      fix (x', y)
      assume h2
      rewrite [pair_with_const_def] at h2
      apply And.intro h2.left
      define
      rewrite [h2.right.left]
      apply And.intro h2.left
      define
      exact h2.right.right
      done
    · -- Proof of fcnl_ons
      apply And.intro
      · -- Proof of fcnl_on
        define
        fix x
        assume h2
        exists_unique
        · -- Existence
          apply Exists.intro (x, b)
          rewrite [pair_with_const_def]
          apply And.intro h2
          apply And.intro
          rfl
          rfl
          done
        · -- Uniqueness
          fix (x1, y1)
          fix (x2, y2)
          assume h3; assume h4
          rewrite [pair_with_const_def] at h3
          rewrite [pair_with_const_def] at h4
          rewrite [h3.right.left, h3.right.right, h4.right.left, h4.right.right]
          rfl
          done
        done
      · -- Proof of fcnl_on invRel
        define
        fix (x, y)
        assume h2
        define at h2
        exists_unique
        · -- Existence
          apply Exists.intro x
          rewrite [invRel_def, pair_with_const_def]
          apply And.intro h2.left
          apply And.intro _ h2.right
          rfl
          done
        · -- Uniqueness
          fix x1; fix x2
          assume h3; assume h4
          rewrite [invRel_def, pair_with_const_def] at h3
          rewrite [invRel_def, pair_with_const_def] at h4
          rewrite [←h3.right.left, ←h4.right.left]
          rfl
          done
        done
      done
    done
  exact Theorem_8_1_3_3 h1 h2
  done
-/

lemma Set_prod_inter {A B : Type} (X : Set A) (Y Z : Set B) :
    X ×ₛ Y ∩ X ×ₛ Z = X ×ₛ (Y ∩ Z) := by
  apply Set.ext
  fix (a, b)
  define : (a, b) ∈ X ×ₛ Y ∩ X ×ₛ Z
  rewrite [Set_prod_def, Set_prod_def, Set_prod_def]
  define : b ∈ Y ∩ Z
  rewrite [and_and_and_comm, and_self]
  rfl
  done

lemma Set_prod_empty {A B : Type} (X : Set A) {Y : Set B} (h : empty Y) :
    empty (X ×ₛ Y) := by
  define
  contradict h with h1
  obtain ((a, b) : A × B) h2 from h1
  rewrite [Set_prod_def] at h2
  exact Exists.intro b h2.right
  done

lemma Set_prod_union {A B : Type} (X : Set A) (Y Z : Set B) :
    X ×ₛ Y ∪ X ×ₛ Z = X ×ₛ (Y ∪ Z) := by
  apply Set.ext
  fix (a, b)
  define : (a, b) ∈ X ×ₛ Y ∪ X ×ₛ Z
  rewrite [Set_prod_def, Set_prod_def, Set_prod_def]
  define : b ∈ Y ∪ Z
  rewrite [and_or_left]
  rfl
  done

theorem Exercise_8_1_22 {A B : Type} {X : Set A} {m : Nat} (h1 : numElts X m) :
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

/- phi agrees with numElts -/
def Set_rp_below (m : Nat) : Set Nat := { n : Nat | rel_prime m n ∧ n < m }

lemma Set_rp_below_def (a m : Nat) : a ∈ Set_rp_below m ↔ rel_prime m a ∧ a < m := by rfl

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

lemma phi_eq_numElts (m : Nat) :
    numElts (Set_rp_below m) (phi m) := by
  have h1 : ∀ (n : Nat), n ∈ Set_rp_below m → n < m := by
    fix n
    assume h2
    define at h2
    exact h2.right
    done
  have h2 : m ≤ m := by linarith
  have h3 := neb_nrpb m h2
  rewrite [numElts_def, phi_def]
  exact bdd_subset_nat h1 h3
  done

/- phi multiplicative -/
-- From Chapter 7 Exercises:
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

lemma congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := by
  rewrite [←cc_eq_iff_congr] at h1
  rewrite [←Theorem_7_3_7, ←Theorem_7_3_7, h1]
  rfl
  done

lemma rel_prime_mod (m a : Nat) : rel_prime m (a % m) ↔ rel_prime m a := by
  have h1 : a ≡ a % m (MOD m) := congr_mod_mod m a
  rewrite [Int.ofNat_mod_ofNat] at h1
  exact (congr_rel_prime h1).symm
  done

lemma mod_elt_Set_rp_below {a m : Nat} [NeZero m] (h1 : rel_prime m a) :
    a % m ∈ Set_rp_below m := by
  define
  rewrite [rel_prime_mod]
  exact And.intro h1 (mod_nonzero_lt a (NeZero.ne m))
  done

lemma Lemma_7_4_7_aux {m n : Nat} {s t : Int} (h : s * m + t * n = 1) (a b : Nat) :
    t * n * a + s * m * b ≡ a (MOD m) := by
  define
  apply Exists.intro (s * (b - a))
  exact
    calc t * n * a + s * m * b - a
      _ = (t * n - 1) * a + s * m * b := by ring
      _ = (t * n - (s * m + t * n)) * a + s * m * b := by rw [h]
      _ = m * (s * (b - a)) := by ring
  done

lemma Lemma_7_4_7 {m n : Nat} [NeZero m] [NeZero n] (h1 : rel_prime m n) (a b : Nat) :
    ∃ (r : Nat), r < m * n ∧ r ≡ a (MOD m) ∧ r ≡ b (MOD n) := by
  set s : Int := gcd_c1 m n
  set t : Int := gcd_c2 m n
  have h4 : s * m + t * n = gcd m n := gcd_lin_comb n m
  define at h1
  rewrite [h1, Nat.cast_one] at h4
  set x : Int := t * n * a + s * m * b
  have h5 : x ≡ a (MOD m) := Lemma_7_4_7_aux h4 a b
  have h6 : t * n + s * m = 1 := by
    rewrite [←h4]
    ring
    done
  have h7 : s * m * b + t * n * a = x := by ring
  have h8 := Lemma_7_4_7_aux h6 b a
  rewrite [h7] at h8
  have h9 := mul_ne_zero (NeZero.ne m) (NeZero.ne n)
  rewrite [←neZero_iff] at h9
  have h10 := mod_cmpl_res (m * n) x
  have h11 := h10.right
  rewrite [←Int.toNat_of_nonneg h10.left, Nat.cast_lt] at h11
  set r : Nat := Int.toNat (x % ↑(m * n))
  apply Exists.intro r
  apply And.intro h11.left
  have h12 : r ≡ x (MOD (m * n)) := congr_symm h11.right
  rewrite [Lemma_7_4_5 _ _ h1] at h12
  apply And.intro
  · -- Proof that r ≡ a (MOD m)
    exact congr_trans h12.left h5
    done
  · -- Proof that r ≡ b (MOD m)
    exact congr_trans h12.right h8
    done
  done

def mod_mod (m n a : Nat) : Nat × Nat := (a % m, a % n)

lemma mod_mod_def (m n a : Nat) : mod_mod m n a = (a % m, a % n) := by rfl

lemma left_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero m :=
  neZero_iff.rtl (left_ne_zero_of_mul h)

lemma right_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero n :=
  neZero_iff.rtl (right_ne_zero_of_mul h)

lemma mod_mod_one_one_on {m n : Nat} (h1 : rel_prime m n) :
    one_one_on (mod_mod m n) (Set_rp_below (m * n)) := by
  define
  fix a1; fix a2
  assume h2; assume h3; assume h4
  define at h2; define at h3
  rewrite [mod_mod_def, mod_mod_def] at h4
  have h5 : m * n ≠ 0 := by linarith
  have h6 : NeZero m := left_NeZero_of_mul h5
  have h7 : NeZero n := right_NeZero_of_mul h5
  have h8 := Prod.mk.inj h4
  rewrite [←congr_iff_mod_eq, ←congr_iff_mod_eq] at h8
  rewrite [←Lemma_7_4_5 _ _ h1] at h8
  rewrite [congr_iff_mod_eq] at h8
  rewrite [Nat.mod_eq_of_lt h2.right, Nat.mod_eq_of_lt h3.right] at h8
  exact h8
  done

lemma mod_mod_image {m n : Nat} (h1 : rel_prime m n) :
    image (mod_mod m n) (Set_rp_below (m * n)) =
      (Set_rp_below m) ×ₛ (Set_rp_below n) := by
  apply Set.ext
  fix (b, c)
  apply Iff.intro
  · -- (→)
    assume h2
    define at h2
    obtain a h3 from h2
    rewrite [Set_rp_below_def, mod_mod_def] at h3
    have h4 := h3.left.left
    rewrite [Lemma_7_4_6] at h4
    have h5 := Prod.mk.inj h3.right
    define
    rewrite [←h5.left, ←h5.right]
    have h6 : m * n ≠ 0 := by linarith
    have h7 : NeZero m := left_NeZero_of_mul h6
    have h8 : NeZero n := right_NeZero_of_mul h6
    apply And.intro
    · -- Proof that a % m ∈ Set_rp_below m
      exact mod_elt_Set_rp_below h4.left
      done
    · -- Proof that a % n ∈ Set_rp_below n
      exact mod_elt_Set_rp_below h4.right
      done
    done
  · -- (←)
    assume h2
    rewrite [Set_prod_def, Set_rp_below_def, Set_rp_below_def] at h2
    define
    have h3 : m ≠ 0 := by linarith
    have h4 : n ≠ 0 := by linarith
    rewrite [←neZero_iff] at h3
    rewrite [←neZero_iff] at h4
    obtain a h5 from Lemma_7_4_7 h1 b c
    apply Exists.intro a
    rewrite [Set_rp_below_def, mod_mod_def]
    apply And.intro
    · --
      apply And.intro _ h5.left
      rewrite [Lemma_7_4_6]
      rewrite [congr_rel_prime h5.right.left, congr_rel_prime h5.right.right]
      exact And.intro h2.left.left h2.right.left
      done
    · --
      rewrite [congr_iff_mod_eq, congr_iff_mod_eq] at h5
      rewrite [h5.right.left, h5.right.right]
      rewrite [Nat.mod_eq_of_lt h2.left.right, Nat.mod_eq_of_lt h2.right.right]
      rfl
      done
    done
  done

lemma Lemma_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    Set_rp_below (m * n) ∼ (Set_rp_below m) ×ₛ (Set_rp_below n) := by
  have h2 := equinum_image (mod_mod_one_one_on h1)
  rewrite [mod_mod_image h1] at h2
  exact h2
  done

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

lemma Lemma_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    equinum (Set_rp_below (m * n)) (Set_prod (Set_rp_below m) (Set_rp_below n)) := by
  define
  apply Exists.intro (rp_mod_mod m n)
  define
  apply And.intro (rp_mod_mod_rel_within h1)
  exact And.intro (rp_mod_mod_fcnl h1) (rp_mod_mod_inv_fcnl h1)
  done
-/

theorem Theorem_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    phi (m * n) = (phi m) * (phi n) := by
  have h2 := phi_eq_numElts m
  have h3 := phi_eq_numElts n
  have h4 := phi_eq_numElts (m * n)
  have h5 := eq_numElts_of_equinum (Lemma_7_4_4 h1) h4
  have h6 := Exercise_8_1_22 h2 h3
  exact Exercise_8_1_6b h5 h6
  done

-- *** Try using subtypes
/-
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
-/