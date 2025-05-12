/- Copyright 2023-2025 Daniel J. Velleman -/

import HTPILib.Chap7
namespace HTPI

open Classical

/- Definitions -/
def fnz (n : Nat) : Int := if 2 ∣ n then ↑(n / 2) else -↑((n + 1) / 2)

def fzn (a : Int) : Nat :=
  if a ≥ 0 then 2 * Int.toNat a else 2 * Int.toNat (-a) - 1

def tri (k : Nat) : Nat := k * (k + 1) / 2

def fnnn (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.1

noncomputable def num_elts_below (A : Set Nat) (m : Nat) : Nat :=
  match m with
    | 0 => 0
    | n + 1 => if n ∈ A then (num_elts_below A n) + 1
                else num_elts_below A n

def smallest_preimage_graph {U : Type}
  (g : Nat → U) (A : Set U) : Set (A × Nat) :=
  {(x, n) : A × Nat | g n = x.val ∧ ∀ (m : Nat), g m = x.val → n ≤ m}

def fqn (q : Rat) : Nat := fnnn (fzn q.num, q.den)

def set_rp_below (m : Nat) : Set Nat := {n : Nat | rel_prime m n ∧ n < m}

def func_prod {U V W X : Type} (f : U → V) (g : W → X)
  (p : U × W) : V × X := (f p.1, g p.2)

def set_prod {U V : Type} (A : Set U) (B : Set V) : Set (U × V) :=
  {(a, b) : U × V | a ∈ A ∧ b ∈ B}

notation:75 A:75 " ×ₛ " B:75 => set_prod A B

lemma elt_set_prod {U V : Type} {A : Set U} {B : Set V} (p : ↑A × ↑B) :
    (p.1.val, p.2.val) ∈ A ×ₛ B := And.intro p.1.property p.2.property

def prod_type_to_prod_set {U V : Type}
  (A : Set U) (B : Set V) (p : ↑A × ↑B) : ↑(A ×ₛ B) :=
  Subtype_elt (elt_set_prod p)

def prod_set_to_prod_type {U V : Type}
  (A : Set U) (B : Set V) (p : ↑(A ×ₛ B)) : ↑A × ↑B :=
  (Subtype_elt p.property.left, Subtype_elt p.property.right)

def qr (n a : Nat) : Nat × Nat := (a / n, a % n)

def mod_mod (m n a : Nat) : Nat × Nat := (a % m, a % n)

def seq {U : Type} (A : Set U) : Set (List U) :=
  {l : List U | ∀ x ∈ l, x ∈ A}

def seq_by_length {U : Type} (A : Set U) (n : Nat) : Set (List U) :=
  {l : List U | l ∈ seq A ∧ l.length = n}

def seq_cons (U : Type) (p : U × (List U)) : List U := p.1 :: p.2

def sbl_set {U : Type} (A : Set U) : Set (Set (List U)) :=
  {S : Set (List U) | ∃ (n : Nat), seq_by_length A n = S}

def csb_func_graph {U V : Type}
  (f : U → V) (g : V → U) (X : Set U) : Set (U × V) :=
  {(x, y) : U × V | (x ∈ X ∧ f x = y) ∨ (x ∉ X ∧ g y = x)}

/- Section 8.1 -/
#eval [fnz 0, fnz 1, fnz 2, fnz 3, fnz 4, fnz 5, fnz 6]
  --Answer: [0, -1, 1, -2, 2, -3, 3]

#eval [fzn 0, fzn (-1), fzn 1, fzn (-2), fzn 2, fzn (-3), fzn 3]
  --Answer: [0, 1, 2, 3, 4, 5, 6]

lemma fnz_even (k : Nat) : fnz (2 * k) = ↑k := by
  have h1 : 2 ∣ 2 * k := by
    apply Exists.intro k
    rfl
    done
  have h2 : 0 < 2 := by linarith
  show fnz (2 * k) = ↑k from
    calc fnz (2 * k)
      _ = ↑(2 * k / 2) := if_pos h1
      _ = ↑k := by rw [Nat.mul_div_cancel_left k h2]
  done

lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := sorry

lemma fzn_nat (k : Nat) : fzn ↑k = 2 * k := by rfl

lemma fzn_neg_succ_nat (k : Nat) : fzn (-↑(k + 1)) = 2 * k + 1 := by rfl

--From exercises of Section 6.1
theorem Exercise_6_1_16a1 : ∀ (n : Nat), nat_even n ∨ nat_odd n := sorry

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

theorem N_equinum_Z : Nat ∼ Int :=
  Exists.intro fnz (And.intro fnz_one_one fnz_onto)

theorem Z_equinum_N : Int ∼ Nat :=
  Exists.intro fzn (And.intro fzn_one_one fzn_onto)

lemma fnnn_def (a b : Nat) : fnnn (a, b) = tri (a + b) + a := by rfl

#eval [fnnn (0, 0), fnnn (0, 1), fnnn (1, 0),
  fnnn (0, 2), fnnn (1, 1), fnnn (2, 0)]
  --Answer: [0, 1, 2, 3, 4, 5]

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

theorem NxN_equinum_N : (Nat × Nat) ∼ Nat :=
  Exists.intro fnnn (And.intro fnnn_one_one fnnn_onto)

lemma neb_base (A : Set Nat) : num_elts_below A 0 = 0 := by rfl

lemma neb_step_elt {A : Set Nat} {n : Nat} (h : n ∈ A) :
    num_elts_below A (n + 1) = num_elts_below A n + 1 := if_pos h

lemma neb_step_not_elt {A : Set Nat} {n : Nat} (h : n ∉ A) :
    num_elts_below A (n + 1) = num_elts_below A n := if_neg h

lemma neb_increase {A : Set Nat} {n : Nat} (h1 : n ∈ A) :
    ∀ ⦃m : Nat⦄, m ≥ n + 1 → num_elts_below A n < num_elts_below A m := by
  by_induc
  · -- Base Case
    rewrite [neb_step_elt h1]
    linarith
    done
  · -- Induction Step
    fix m : Nat
    assume h2 : m ≥ n + 1
    assume ih : num_elts_below A n < num_elts_below A m
    by_cases h3 : m ∈ A
    · -- Case 1. h3 : m ∈ A
      rewrite [neb_step_elt h3]
      linarith
      done
    · -- Case 2. h3 : m ∉ A
      rewrite [neb_step_not_elt h3]
      show num_elts_below A n < num_elts_below A m from ih
      done
    done
  done

lemma le_of_neb_eq {A : Set Nat} {n1 n2 : Nat}
    (h1 : num_elts_below A n1 = num_elts_below A n2) (h2 : n2 ∈ A) :
    n1 ≤ n2 := by
  by_contra h3
  have h4 : n1 ≥ n2 + 1 := by linarith
  have h5 : num_elts_below A n2 < num_elts_below A n1 := neb_increase h2 h4
  linarith
  done

lemma neb_one_one_on (A : Set Nat) :
    one_one_on (num_elts_below A) A := by
  fix n1 : Nat; fix n2 : Nat
  assume h1 : n1 ∈ A
  assume h2 : n2 ∈ A
  assume h3 : num_elts_below A n1 = num_elts_below A n2
  have h4 : n1 ≤ n2 := le_of_neb_eq h3 h2
  have h5 : n2 ≤ n1 := le_of_neb_eq h3.symm h1
  linarith
  done

lemma neb_not_skip {A : Set Nat} : ∀ ⦃m : Nat⦄,
    ∀ t < num_elts_below A m, t ∈ image (num_elts_below A) A := by
  by_induc
  · -- Base Case
    rewrite [neb_base]
    fix t : Nat
    assume h : t < 0
    linarith
    done
  · -- Induction Step
    fix m : Nat
    assume ih : ∀ t < num_elts_below A m, t ∈ image (num_elts_below A) A
    fix t : Nat
    assume h1 : t < num_elts_below A (m + 1)
    by_cases h2 : m ∈ A
    · -- Case 1. h2 : m ∈ A
      rewrite [neb_step_elt h2] at h1
      by_cases h3 : t = num_elts_below A m
      · -- Case 1.1. h3 : t = num_elts_below A m
        show t ∈ image (num_elts_below A) A from
          Exists.intro m (And.intro h2 h3.symm)
        done
      · -- Case 1.2. h3 : t ≠ num_elts_below A m
        have h4 : t ≤ num_elts_below A m := Nat.le_of_lt_succ h1
        have h5 : t < num_elts_below A m := Nat.lt_of_le_of_ne h4 h3
        show t ∈ image (num_elts_below A) A from ih t h5
        done
      done
    · -- Case 2. h2 : m ∉ A
      rewrite [neb_step_not_elt h2] at h1
      show t ∈ image (num_elts_below A) A from ih t h1
      done
    done
  done

lemma neb_image_bdd {A : Set Nat} {m : Nat} (h : ∀ n ∈ A, n < m) :
    image (num_elts_below A) A = I (num_elts_below A m) := by
  apply Set.ext
  fix t : Nat
  apply Iff.intro
  · -- (→)
    assume h2 : t ∈ image (num_elts_below A) A
    obtain (n : Nat) (h3 : n ∈ A ∧ num_elts_below A n = t) from h2
    define
    rewrite [←h3.right]
    show num_elts_below A n < num_elts_below A m from
      neb_increase h3.left (h n h3.left)
    done
  · -- (←)
    assume h2 : t ∈ I (num_elts_below A m)
    define at h2
    show t ∈ image (num_elts_below A) A from neb_not_skip t h2
    done
  done

lemma bdd_subset_nat {A : Set Nat} {m : Nat}
    (h : ∀ n ∈ A, n < m) : I (num_elts_below A m) ∼ A := by
  have h2 : A ∼ image (num_elts_below A) A :=
    equinum_image (neb_one_one_on A)
  rewrite [neb_image_bdd h] at h2        --h2 : A ∼ I (num_elts_below A m)
  show I (num_elts_below A m) ∼ A from Theorem_8_1_3_2 h2
  done

lemma neb_unbdd_onto {A : Set Nat}
    (h : ∀ (m : Nat), ∃ n ∈ A, n ≥ m) :
    onto (func_restrict (num_elts_below A) A) := by
  define
  by_induc
  · -- Base Case
    obtain (m : Nat) (h2 : m ∈ A ∧ m ≥ 0) from h 0
    have h3 : 0 < num_elts_below A (m + 1) := by
      rewrite [neb_step_elt h2.left]
      linarith
      done
    obtain (n : Nat) (h4 : n ∈ A ∧ num_elts_below A n = 0) from
      neb_not_skip 0 h3
    set nA : A := Subtype_elt h4.left
    apply Exists.intro nA
    show func_restrict (num_elts_below A) A nA = 0 from h4.right
    done
  · -- Induction Step
    fix s : Nat
    assume ih : ∃ (x : A), func_restrict (num_elts_below A) A x = s
    obtain (m1 : A) (h2 : func_restrict (num_elts_below A) A m1 = s) from ih
    rewrite [fr_def] at h2
    obtain (m2 : Nat) (h3 : m2 ∈ A ∧ m2 ≥ m1.val + 1) from h (m1.val + 1)
    have h4 : num_elts_below A m1.val < num_elts_below A m2 :=
      neb_increase m1.property h3.right
    rewrite [h2] at h4
    have h5 : s + 1 < num_elts_below A m2 + 1 := by rel [h4]
    rewrite [←neb_step_elt h3.left] at h5
    obtain (n : Nat) (h6 : n ∈ A ∧ num_elts_below A n = s + 1) from
      neb_not_skip (s + 1) h5
    set nA : A := Subtype_elt h6.left
    apply Exists.intro nA
    show func_restrict (num_elts_below A) A nA = s + 1 from h6.right
    done
  done

lemma unbdd_subset_nat {A : Set Nat}
    (h : ∀ (m : Nat), ∃ n ∈ A, n ≥ m) :
    denum A := by
  rewrite [denum_def]
  set f : A → Nat := func_restrict (num_elts_below A) A
  have h1 : one_to_one f :=
    fr_one_one_of_one_one_on (neb_one_one_on A)
  have h2 : onto f := neb_unbdd_onto h
  have h3 : A ∼ Nat := Exists.intro f (And.intro h1 h2)
  show Nat ∼ A from Theorem_8_1_3_2 h3
  done

theorem set_nat_ctble (A : Set Nat) : ctble A := by
  define          --Goal : finite A ∨ denum A
  by_cases h1 : ∃ (m : Nat), ∀ n ∈ A, n < m
  · -- Case 1. h1 : ∃ (m : Nat), ∀ n ∈ A, n < m
    apply Or.inl  --Goal : finite A
    obtain (m : Nat) (h2 : ∀ n ∈ A, n < m) from h1
    define
    apply Exists.intro (num_elts_below A m)
    show I (num_elts_below A m) ∼ A from bdd_subset_nat h2
    done
  · -- Case 2. h1 : ¬∃ (m : Nat), ∀ n ∈ A, n < m
    apply Or.inr  --Goal : denum A
    push_neg at h1
      --This tactic converts h1 to ∀ (m : Nat), ∃ n ∈ A, m ≤ n
    show denum A from unbdd_subset_nat h1
    done
  done

def Univ (U : Type) : Set U := {x : U | True}

lemma elt_univ {U : Type} (x : U) : x ∈ Univ U := by
  define   --Goal : True
  trivial
  done

lemma onto_iff_range_eq_univ {U V : Type} (f : U → V) :
    onto f ↔ range f = Univ V := sorry

lemma univ_equinum_type (U : Type) : Univ U ∼ U := by
  set f : U → U := id
  have h1 : one_to_one f := id_one_one U
  have h2 : onto f := id_onto U
  rewrite [onto_iff_range_eq_univ] at h2  --h2 : range f = Univ U
  have h3 : U ∼ range f := equinum_range h1
  rewrite [h2] at h3
  show Univ U ∼ U from Theorem_8_1_3_2 h3
  done

lemma ctble_of_ctble_equinum {U V : Type}
    (h1 : U ∼ V) (h2 : ctble U) : ctble V := sorry

theorem ctble_iff_set_nat_equinum (U : Type) :
    ctble U ↔ ∃ (J : Set Nat), J ∼ U := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble U
    define at h1  --h1 : finite U ∨ denum U
    by_cases on h1
    · -- Case 1. h1 : finite U
      define at h1  --h1 : ∃ (n : Nat), I n ∼ U
      obtain (n : Nat) (h2 : I n ∼ U) from h1
      show ∃ (J : Set Nat), J ∼ U from Exists.intro (I n) h2
      done
    · -- Case 2. h1 : denum U
      rewrite [denum_def] at h1  --h1 : Nat ∼ U
      have h2 : Univ Nat ∼ Nat := univ_equinum_type Nat
      apply Exists.intro (Univ Nat)
      show Univ Nat ∼ U from Theorem_8_1_3_3 h2 h1
      done
    done
  · -- (←)
    assume h1 : ∃ (J : Set Nat), J ∼ U
    obtain (J : Set Nat) (h2 : J ∼ U) from h1
    have h3 : ctble J := set_nat_ctble J
    show ctble U from ctble_of_ctble_equinum h2 h3
    done
  done

theorem Theorem_8_1_5_1_to_2 {U : Type} {A : Set U} (h : ctble A) :
    empty A ∨ ∃ (f : Nat → U), A ⊆ range f := by
  or_right with h1                          --h1 : ∃ (x : U), x ∈ A
  obtain (a : U) (h2 : a ∈ A) from h1
  rewrite [ctble_iff_set_nat_equinum] at h  --h : ∃ (J : Set Nat), J ∼ A
  obtain (J : Set Nat) (h3 : J ∼ A) from h
  obtain (f : Nat → U) (h4 : one_one_on f J ∧ image f J = A) from
    type_to_type_of_equinum h3 a
  apply Exists.intro f                      --Goal : A ⊆ range f
  fix y : U
  assume h5 : y ∈ A
  rewrite [←h4.right] at h5
  define at h5
  obtain (n : Nat) (h6 : n ∈ J ∧ f n = y) from h5
  rewrite [←h6.right]
  show f n ∈ range f from elt_range f n
  done

lemma spg_is_func_graph {U : Type} {g : Nat → U} {A : Set U}
    (h : A ⊆ range g) : is_func_graph (smallest_preimage_graph g A) := by
  define
  fix x : A
  exists_unique
  · -- Existence
    set W : Set Nat := {n : Nat | g n = x.val}
    have h1 : ∃ (n : Nat), n ∈ W := h x.property
    show ∃ (y : Nat), (x, y) ∈ smallest_preimage_graph g A from
      well_ord_princ W h1
    done
  · -- Uniqueness
    fix n1 : Nat; fix n2 : Nat
    assume h1 : (x, n1) ∈ smallest_preimage_graph g A
    assume h2 : (x, n2) ∈ smallest_preimage_graph g A
    define at h1; define at h2
    have h3 : n1 ≤ n2 := h1.right n2 h2.left
    have h4 : n2 ≤ n1 := h2.right n1 h1.left
    linarith
    done
  done

lemma spg_one_one {U : Type} {g : Nat → U} {A : Set U} {f : A → Nat}
    (h : graph f = smallest_preimage_graph g A) : one_to_one f := by
  fix a1 : A; fix a2 : A
  assume h1 : f a1 = f a2
  set y : Nat := f a2           --h1 : f a1 = y
  have h2 : f a2 = y := by rfl
  rewrite [←graph_def, h] at h1 --h1 : (a1, y) ∈ smallest_preimage_graph g A
  rewrite [←graph_def, h] at h2 --h2 : (a2, y) ∈ smallest_preimage_graph g A
  define at h1                  --h1 : g y = a1.val ∧ ...
  define at h2                  --h2 : g y = a2.val ∧ ...
  apply Subtype.ext             --Goal : a1.val = a2.val
  rewrite [←h1.left, ←h2.left]
  rfl
  done

theorem Theorem_8_1_5_2_to_3 {U : Type} {A : Set U}
    (h : empty A ∨ ∃ (f : Nat → U), A ⊆ range f) :
    ∃ (f : U → Nat), one_one_on f A := by
  by_cases on h
  · -- Case 1. h : empty A
    set f : U → Nat := constant_func U 0
    apply Exists.intro f
    show one_one_on f A from one_one_on_empty f h
    done
  · -- Case 2. h : ∃ (f : Nat → U), A ⊆ range f
    obtain (g : Nat → U) (h1 : A ⊆ range g) from h
    have h2 : is_func_graph (smallest_preimage_graph g A) :=
      spg_is_func_graph h1
    rewrite [←func_from_graph] at h2
    obtain (F : A → Nat)
      (h3 : graph F = smallest_preimage_graph g A) from h2
    have h4 : one_to_one F := spg_one_one h3
    set f : U → Nat := func_extend F 0
    apply Exists.intro f
    show one_one_on f A from fe_one_one_on_of_one_one h4 0
    done
  done

theorem Theorem_8_1_5_3_to_1 {U : Type} {A : Set U}
    (h1 : ∃ (f : U → Nat), one_one_on f A) :
    ctble A := by
  obtain (f : U → Nat) (h2 : one_one_on f A) from h1
  have h3 : A ∼ image f A := equinum_image h2
  rewrite [ctble_iff_set_nat_equinum]
  show ∃ (J : Set Nat), J ∼ A from
    Exists.intro (image f A) (Theorem_8_1_3_2 h3)
  done

theorem Theorem_8_1_5_2 {U : Type} (A : Set U) :
    ctble A ↔ empty A ∨ ∃ (f : Nat → U), A ⊆ range f := by
  apply Iff.intro Theorem_8_1_5_1_to_2
  assume h1 : empty A ∨ ∃ (f : Nat → U), A ⊆ range f
  have h2 : ∃ (f : U → Nat), one_one_on f A := Theorem_8_1_5_2_to_3 h1
  show ctble A from Theorem_8_1_5_3_to_1 h2
  done

theorem Theorem_8_1_5_3 {U : Type} (A : Set U) :
    ctble A ↔ ∃ (f : U → Nat), one_one_on f A := by
  apply Iff.intro _ Theorem_8_1_5_3_to_1
  assume h1 : ctble A
  have h2 : empty A ∨ ∃ (f : Nat → U), A ⊆ range f := Theorem_8_1_5_1_to_2 h1
  show ∃ (f : U → Nat), one_one_on f A from Theorem_8_1_5_2_to_3 h2
  done

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
  show q1 = q2 from Rat.ext h4 h3.right
  done

lemma range_fqn_unbdd :
    ∀ (m : Nat), ∃ n ∈ range fqn, n ≥ m := by
  fix m : Nat
  set n : Nat := fqn ↑m
  apply Exists.intro n
  apply And.intro
  · -- Proof that n ∈ range fqn
    define
    apply Exists.intro ↑m
    rfl
    done
  · -- Proof that n ≥ m
    show n ≥ m from
      calc n
        _ = tri (2 * m + 1) + 2 * m := by rfl
        _ ≥ m := by linarith
    done
  done

theorem Theorem_8_1_6 : denum Rat := by
  set I : Set Nat := range fqn
  have h1 : Nat ∼ I := unbdd_subset_nat range_fqn_unbdd
  have h2 : Rat ∼ I := equinum_range fqn_one_one
  have h3 : I ∼ Rat := Theorem_8_1_3_2 h2
  show denum Rat from Theorem_8_1_3_3 h1 h3
  done

/- Section 8.1½ -/
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := sorry

lemma set_rp_below_def (a m : Nat) :
    a ∈ set_rp_below m ↔ rel_prime m a ∧ a < m := by rfl

lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := sorry

lemma neb_phi (m : Nat) :
    num_elts_below (set_rp_below m) m = phi m := by
  rewrite [phi_def]
  have h1 : m ≤ m := by linarith
  show num_elts_below (set_rp_below m) m = num_rp_below m m from
    neb_nrpb m h1
  done

lemma phi_is_numElts (m : Nat) :
    numElts (set_rp_below m) (phi m) := by
  rewrite [numElts_def, ←neb_phi m]
    --Goal : I (num_elts_below (set_rp_below m) m) ∼ set_rp_below m
  have h1 : ∀ n ∈ set_rp_below m, n < m := by
    fix n : Nat
    assume h2 : n ∈ set_rp_below m
    define at h2
    show n < m from h2.right
    done
  show I (num_elts_below (set_rp_below m) m) ∼ set_rp_below m from
    bdd_subset_nat h1
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

lemma func_prod_def {U V W X : Type}
    (f : U → V) (g : W → X) (u : U) (w : W) :
    func_prod f g (u, w) = (f u, g w) := by rfl

theorem Theorem_8_1_2_1_type {U V W X : Type}
    (h1 : U ∼ V) (h2 : W ∼ X) : (U × W) ∼ (V × X) := by
  obtain (f : U → V) (h3 : one_to_one f ∧ onto f) from h1
  obtain (g : W → X) (h4 : one_to_one g ∧ onto g) from h2
  apply Exists.intro (func_prod f g)
  apply And.intro
  · -- Proof of one_to_one (func_prod f g)
    fix (u1, w1) : U × W; fix (u2, w2) : U × W
    assume h5 : func_prod f g (u1, w1) = func_prod f g (u2, w2)
    rewrite [func_prod_def, func_prod_def] at h5
    have h6 : f u1 = f u2 ∧ g w1 = g w2 := Prod.mk.inj h5
    have h7 : u1 = u2 := h3.left u1 u2 h6.left
    have h8 : w1 = w2 := h4.left w1 w2 h6.right
    rewrite [h7, h8]
    rfl
    done
  · -- Proof of onto (func_prod f g)
    fix (v, x) : V × X
    obtain (u : U) (h5 : f u = v) from h3.right v
    obtain (w : W) (h6 : g w = x) from h4.right x
    apply Exists.intro (u, w)
    rewrite [func_prod_def, h5, h6]
    rfl
  done

lemma set_prod_def {U V : Type} (A : Set U) (B : Set V) (a : U) (b : V) :
    (a, b) ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B := by rfl

lemma set_prod_equinum_type_prod {U V : Type} (A : Set U) (B : Set V) :
    ↑(A ×ₛ B) ∼ (↑A × ↑B) := by
  set F : ↑(A ×ₛ B) → ↑A × ↑B := prod_set_to_prod_type A B
  set G : ↑A × ↑B → ↑(A ×ₛ B) := prod_type_to_prod_set A B
  have h1 : F ∘ G = id := by rfl
  have h2 : G ∘ F = id := by rfl
  have h3 : one_to_one F := Theorem_5_3_3_1 F G h2
  have h4 : onto F := Theorem_5_3_3_2 F G h1
  show ↑(A ×ₛ B) ∼ (↑A × ↑B) from Exists.intro F (And.intro h3 h4)
  done

theorem Theorem_8_1_2_1_set
    {U V W X : Type} {A : Set U} {B : Set V} {C : Set W} {D : Set X}
    (h1 : A ∼ B) (h2 : C ∼ D) : A ×ₛ C ∼ B ×ₛ D := by
  have h3 : ↑(A ×ₛ C) ∼ (↑A × ↑C) := set_prod_equinum_type_prod A C
  have h4 : (↑A × ↑C) ∼ (↑B × ↑D) := Theorem_8_1_2_1_type h1 h2
  have h5 : ↑(B ×ₛ D) ∼ (↑B × ↑D) := set_prod_equinum_type_prod B D
  have h6 : (↑B × ↑D) ∼ ↑(B ×ₛ D) := Theorem_8_1_3_2 h5
  have h7 : ↑(A ×ₛ C) ∼ (↑B × ↑D) := Theorem_8_1_3_3 h3 h4
  show ↑(A ×ₛ C) ∼ ↑(B ×ₛ D) from Theorem_8_1_3_3 h7 h6
  done

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
    image (qr n) (I (m * n)) = (I m) ×ₛ (I n) := sorry

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := by
  rewrite [←qr_image m n]
  show I (m * n) ∼ image (qr n) (I (m * n)) from
    equinum_image (one_one_on_of_one_one (qr_one_one n) (I (m * n)))
  done

theorem numElts_prod {U V : Type} {A : Set U} {B : Set V} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts B n) : numElts (A ×ₛ B) (m * n) := by
  rewrite [numElts_def] at h1     --h1 : I m ∼ A
  rewrite [numElts_def] at h2     --h2 : I n ∼ B
  rewrite [numElts_def]           --Goal : I (m * n) ∼ A ×ₛ B
  have h3 : I m ×ₛ I n ∼ A ×ₛ B := Theorem_8_1_2_1_set h1 h2
  have h4 : I (m * n) ∼ I m ×ₛ I n := I_prod m n
  show I (m * n) ∼ A ×ₛ B from Theorem_8_1_3_3 h4 h3
  done

lemma mod_mod_def (m n a : Nat) : mod_mod m n a = (a % m, a % n) := by rfl

--From exercises of Section 7.3
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

--From exercises of Section 7.4
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

lemma left_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero m :=
  neZero_iff.rtl (left_ne_zero_of_mul h)

lemma right_NeZero_of_mul {m n : Nat} (h : m * n ≠ 0) : NeZero n :=
  neZero_iff.rtl (right_ne_zero_of_mul h)

lemma mod_mod_one_one_on {m n : Nat} (h1 : rel_prime m n) :
    one_one_on (mod_mod m n) (set_rp_below (m * n)) := by
  define
  fix a1 : Nat; fix a2 : Nat
  assume h2 : a1 ∈ set_rp_below (m * n)
  assume h3 : a2 ∈ set_rp_below (m * n)
  assume h4 : mod_mod m n a1 = mod_mod m n a2   --Goal : a1 = a2
  define at h2; define at h3
  rewrite [mod_mod_def, mod_mod_def] at h4
  have h5 : a1 % m = a2 % m ∧ a1 % n = a2 % n := Prod.mk.inj h4
  have h6 : m * n ≠ 0 := by linarith
  have h7 : NeZero m := left_NeZero_of_mul h6
  have h8 : NeZero n := right_NeZero_of_mul h6
  rewrite [←congr_iff_mod_eq_Nat, ←congr_iff_mod_eq_Nat] at h5
      --h5 : ↑a1 ≡ ↑a2 (MOD m) ∧ ↑a1 ≡ ↑a2 (MOD n)
  rewrite [←Lemma_7_4_5 _ _ h1] at h5  --h5 : ↑a1 ≡ ↑a2 (MOD m * n)
  rewrite [congr_iff_mod_eq_Nat] at h5 --h5 : a1 % (m * n) = a2 % (m * n)
  rewrite [Nat.mod_eq_of_lt h2.right, Nat.mod_eq_of_lt h3.right] at h5
  show a1 = a2 from h5
  done

lemma mod_elt_set_rp_below {a m : Nat} [NeZero m] (h1 : rel_prime m a) :
    a % m ∈ set_rp_below m := by
  define                  --Goal : rel_prime m (a % m) ∧ a % m < m
  rewrite [rel_prime_mod] --Goal : rel_prime m a ∧ a % m < m
  show rel_prime m a ∧ a % m < m from
    And.intro h1 (mod_nonzero_lt a (NeZero.ne m))
  done

lemma mod_mod_image {m n : Nat} (h1 : rel_prime m n) :
    image (mod_mod m n) (set_rp_below (m * n)) =
      (set_rp_below m) ×ₛ (set_rp_below n) := by
  apply Set.ext
  fix (b, c) : Nat × Nat
  apply Iff.intro
  · -- (→)
    assume h2 : (b, c) ∈ image (mod_mod m n) (set_rp_below (m * n))
    define at h2
    obtain (a : Nat)
      (h3 : a ∈ set_rp_below (m * n) ∧ mod_mod m n a = (b, c)) from h2
    rewrite [set_rp_below_def, mod_mod_def] at h3
    have h4 : rel_prime (m * n) a := h3.left.left
    rewrite [Lemma_7_4_6] at h4   --h4 : rel_prime m a ∧ rel_prime n a
    have h5 : a % m = b ∧ a % n = c := Prod.mk.inj h3.right
    define
    rewrite [←h5.left, ←h5.right]
      --Goal : a % m ∈ set_rp_below m ∧ a % n ∈ set_rp_below n
    have h6 : m * n ≠ 0 := by linarith
    have h7 : NeZero m := left_NeZero_of_mul h6
    have h8 : NeZero n := right_NeZero_of_mul h6
    apply And.intro
    · -- Proof that a % m ∈ set_rp_below m
      show a % m ∈ set_rp_below m from mod_elt_set_rp_below h4.left
      done
    · -- Proof that a % n ∈ set_rp_below n
      show a % n ∈ set_rp_below n from mod_elt_set_rp_below h4.right
      done
    done
  · -- (←)
    assume h2 : (b, c) ∈ set_rp_below m ×ₛ set_rp_below n
    rewrite [set_prod_def, set_rp_below_def, set_rp_below_def] at h2
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
    · -- Proof of a ∈ set_rp_below (m * n)
      define                  --Goal : rel_prime (m * n) a ∧ a < m * n
      apply And.intro _ h5.left
      rewrite [Lemma_7_4_6]   --Goal : rel_prime m a ∧ rel_prime n a
      rewrite [congr_rel_prime h5.right.left,
        congr_rel_prime h5.right.right]
      show rel_prime m b ∧ rel_prime n c from
        And.intro h2.left.left h2.right.left
      done
    · -- Proof of mod_mod m n a = (b, c)
      rewrite [congr_iff_mod_eq_Nat, congr_iff_mod_eq_Nat] at h5
      rewrite [mod_mod_def, h5.right.left, h5.right.right]
        --Goal : (b % m, c % n) = (b, c)
      rewrite [Nat.mod_eq_of_lt h2.left.right,
        Nat.mod_eq_of_lt h2.right.right]
      rfl
      done
    done
  done

lemma set_rp_below_prod {m n : Nat} (h1 : rel_prime m n) :
    set_rp_below (m * n) ∼ (set_rp_below m) ×ₛ (set_rp_below n) := by
  rewrite [←mod_mod_image h1]
  show set_rp_below (m * n) ∼
    image (mod_mod m n) (set_rp_below (m * n)) from
    equinum_image (mod_mod_one_one_on h1)
  done

lemma eq_numElts_of_equinum {U V : Type} {A : Set U} {B : Set V} {n : Nat}
    (h1 : A ∼ B) (h2 : numElts A n) : numElts B n := by
  rewrite [numElts_def] at h2   --h2 : I n ∼ A
  rewrite [numElts_def]         --Goal : I n ∼ B
  show I n ∼ B from Theorem_8_1_3_3 h2 h1
  done

theorem Theorem_7_4_4 {m n : Nat} (h1 : rel_prime m n) :
    phi (m * n) = (phi m) * (phi n) := by
  have h2 : numElts (set_rp_below m) (phi m) := phi_is_numElts m
  have h3 : numElts (set_rp_below n) (phi n) := phi_is_numElts n
  have h4 : numElts (set_rp_below (m * n)) (phi (m * n)) :=
    phi_is_numElts (m * n)
  have h5 : numElts (set_rp_below m ×ₛ set_rp_below n) (phi (m * n)) :=
    eq_numElts_of_equinum (set_rp_below_prod h1) h4
  have h6 : numElts (set_rp_below m ×ₛ set_rp_below n) (phi m * phi n) :=
    numElts_prod h2 h3
  show phi (m * n) = phi m * phi n from Exercise_8_1_6b h5 h6
  done

/- Section 8.2 -/
--From exercises of Section 8.1
theorem ctble_set_of_ctble_type {U : Type}
    (h : ctble U) (A : Set U) : ctble A := sorry

theorem NxN_denum : denum (Nat × Nat) := Theorem_8_1_3_2 NxN_equinum_N

theorem Theorem_8_2_1_1 {U V : Type} {A : Set U} {B : Set V}
    (h1 : ctble A) (h2 : ctble B) : ctble (A ×ₛ B) := by
  rewrite [ctble_iff_set_nat_equinum] at h1
  rewrite [ctble_iff_set_nat_equinum] at h2
  obtain (J : Set Nat) (h3 : J ∼ A) from h1
  obtain (K : Set Nat) (h4 : K ∼ B) from h2
  have h5 : J ×ₛ K ∼ A ×ₛ B := Theorem_8_1_2_1_set h3 h4
  have h6 : ctble (Nat × Nat) := Or.inr NxN_denum
  have h7 : ctble (J ×ₛ K) := ctble_set_of_ctble_type h6 (J ×ₛ K)
  show ctble (A ×ₛ B) from ctble_of_ctble_equinum h5 h7
  done

--From exercises of Section 8.1
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

--From exercises of Section 3.4
theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := sorry

lemma Lemma_8_2_2_1 {U : Type} {F : Set (Set U)} {g : Set U → Nat → U}
    (h1 : ctble F) (h2 : ¬empty F) (h3 : ∀ A ∈ F, A ⊆ range (g A)) :
    ctble (⋃₀ F) := by
  rewrite [Theorem_8_1_5_2] at h1
  disj_syll h1 h2               --h1 : ∃ (f : Nat → Set U), F ⊆ range f
  rewrite [Theorem_8_1_5_2]
  apply Or.inr                  --Goal : ∃ (f : Nat → Set U), ⋃₀F ⊆ range f
  obtain (j : Nat → Set U) (h4 : F ⊆ range j) from h1
  obtain (p : Nat → Nat × Nat) (h5 : one_to_one p ∧ onto p) from NxN_denum
  set f : Nat → U := fun (n : Nat) => g (j (p n).1) (p n).2
  apply Exists.intro f
  fix x : U
  assume h6 : x ∈ ⋃₀ F
  obtain (A : Set U) (h7 : A ∈ F ∧ x ∈ A) from h6
  obtain (n1 : Nat) (h8 : j n1 = A) from h4 h7.left
  obtain (n2 : Nat) (h9 : g A n2 = x) from h3 A h7.left h7.right
  obtain (n : Nat) (h10 : p n = (n1, n2)) from h5.right (n1, n2)
  apply Exists.intro n
  show f n = x from
    calc f n
      _ = g (j (p n).1) (p n).2 := by rfl
      _ = g (j n1) n2 := by rw [h10]
      _ = g A n2 := by rw [h8]
      _ = x := by rw [h9]
  done

lemma Lemma_8_2_2_2 {U : Type} {F : Set (Set U)} (h1 : ∀ A ∈ F, ctble A)
    (h2 : ¬empty F) (h3 : ∀ A ∈ F, ¬empty A):
    ∃ (g : Set U → Nat → U), ∀ A ∈ F, A ⊆ range (g A) := by
  have h4 : ∀ (A : Set U), ∃ (gA : Nat → U),
      A ∈ F → A ⊆ range gA := by
    fix A : Set U
    by_cases h4 : A ∈ F
    · -- Case 1. h4 : A ∈ F
      have h5 : ctble A := h1 A h4
      rewrite [Theorem_8_1_5_2] at h5
      disj_syll h5 (h3 A h4)    --h5 : ∃ (f : Nat → U), A ⊆ range f
      obtain (gA : Nat → U) (h6 : A ⊆ range gA) from h5
      apply Exists.intro gA
      assume h7 : A ∈ F
      show A ⊆ range gA from h6
      done
    · -- Case 2. h4 : A ∉ F
      rewrite [not_empty_iff_exists_elt] at h2
      obtain (A0 : Set U) (h5 : A0 ∈ F) from h2
      have h6 : ¬empty A0 := h3 A0 h5
      rewrite [not_empty_iff_exists_elt] at h6
      obtain (x0 : U) (h7 : x0 ∈ A0) from h6
      set gA : Nat → U := constant_func Nat x0
      apply Exists.intro gA
      contrapos
      assume h8 : A ⊈ range gA
      show A ∉ F from h4
      done
    done
  set g : Set U → Nat → U := fun (A : Set U) => Classical.choose (h4 A)
  apply Exists.intro g
  fix A : Set U
  show A ∈ F → A ⊆ range (g A) from Classical.choose_spec (h4 A)
  done

lemma Lemma_8_2_2_3 {U : Type} {F : Set (Set U)}
    (h1 : ctble F) (h2 : ∀ A ∈ F, ctble A) (h3 : ∀ A ∈ F, ¬empty A) :
    ctble (⋃₀ F) := by
  by_cases h4 : empty F
  · -- Case 1. h4 : empty F
    have h5 : empty (⋃₀ F) := by
      contradict h4 with h5
      rewrite [not_empty_iff_exists_elt] at h5
      obtain (x : U) (h6 : x ∈ ⋃₀ F) from h5
      obtain (A : Set U) (h7 : A ∈ F ∧ x ∈ A) from h6
      show ∃ (x : Set U), x ∈ F from Exists.intro A h7.left
      done
    rewrite [←zero_elts_iff_empty] at h5    --h5 : numElts (⋃₀ F) 0
    define
    apply Or.inl
    rewrite [finite_def]
    show ∃ (n : Nat), numElts (⋃₀ F) n from Exists.intro 0 h5
    done
  · -- Case 2. h4 : ¬empty F
    obtain (g : Set U → Nat → U) (h5 : ∀ A ∈ F, A ⊆ range (g A)) from
      Lemma_8_2_2_2 h2 h4 h3
    show ctble (⋃₀ F) from Lemma_8_2_2_1 h1 h4 h5
    done

lemma remove_empty_subset {U : Type} (F : Set (Set U)) :
    {A : Set U | A ∈ F ∧ ¬empty A} ⊆ F := by
  fix X : Set U
  assume h1 : X ∈ {A : Set U | A ∈ F ∧ ¬empty A}
  define at h1
  show X ∈ F from h1.left
  done

lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := sorry

theorem Theorem_8_2_2 {U : Type} {F : Set (Set U)}
    (h1 : ctble F) (h2 : ∀ A ∈ F, ctble A) : ctble (⋃₀ F) := by
  set G : Set (Set U) := {A : Set U | A ∈ F ∧ ¬empty A}
  have h3 : G ⊆ F := remove_empty_subset F
  have h4 : ⋃₀ G = ⋃₀ F := remove_empty_union_eq F
  rewrite [←h4]
  have h5 : ctble G := Exercise_8_1_17 h3 h1
  have h6 : ∀ A ∈ G, ctble A := by
    fix A : Set U
    assume h6 : A ∈ G
    show ctble A from h2 A (h3 h6)
    done
  have h7 : ∀ A ∈ G, ¬empty A := by
    fix A : Set U
    assume h7 : A ∈ G
    define at h7
    show ¬empty A from h7.right
    done
  show ctble (⋃₀ G) from Lemma_8_2_2_3 h5 h6 h7
  done

lemma seq_def {U : Type} (A : Set U) (l : List U) :
    l ∈ seq A ↔ ∀ x ∈ l, x ∈ A := by rfl

lemma sbl_base {U : Type} (A : Set U) : seq_by_length A 0 = {[]} := by
  apply Set.ext
  fix l : List U
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ seq_by_length A 0
    define at h1   --h1 : l ∈ seq A ∧ l.length = 0
    rewrite [List.length_eq_zero_iff] at h1
    define
    show l = [] from h1.right
    done
  · -- (←)
    assume h1 : l ∈ {[]}
    define at h1     --h1 : l = []
    define           --Goal : l ∈ seq A ∧ l.length = 0
    apply And.intro _ (List.length_eq_zero_iff.rtl h1)
    define           --Goal : ∀ x ∈ l, x ∈ A
    fix x : U
    contrapos
    assume h2 : x ∉ A
    rewrite [h1]
    show x ∉ [] from List.not_mem_nil
    done
  done

lemma seq_cons_def {U : Type} (x : U) (l : List U) :
    seq_cons U (x, l) = x :: l := by rfl

lemma seq_cons_one_one (U : Type) : one_to_one (seq_cons U) := by
  fix (a1, l1) : U × List U; fix (a2, l2) : U × List U
  assume h1 : seq_cons U (a1, l1) = seq_cons U (a2, l2)
  rewrite [seq_cons_def, seq_cons_def] at h1  --h1 : a1 :: l1 = a2 :: l2
  rewrite [List.cons_eq_cons] at h1           --h1 : a1 = a2 ∧ l1 = l2
  rewrite [h1.left, h1.right]
  rfl
  done

lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

lemma Lemma_8_2_4_1 {U : Type} (A : Set U) (n : Nat) :
    A ×ₛ (seq_by_length A n) ∼ seq_by_length A (n + 1) := by
  rewrite [←seq_cons_image A n]
  show A ×ₛ seq_by_length A n ∼
    image (seq_cons U) (A ×ₛ seq_by_length A n) from equinum_image
    (one_one_on_of_one_one (seq_cons_one_one U) (A ×ₛ (seq_by_length A n)))
  done

lemma Lemma_8_2_4_2 {U : Type} {A : Set U} (h1 : ctble A) :
    ∀ (n : Nat), ctble (seq_by_length A n) := by
  by_induc
  · -- Base Case
    rewrite [sbl_base]   --Goal : ctble {[]}
    define
    apply Or.inl         --Goal : finite {[]}
    rewrite [finite_def]
    apply Exists.intro 1 --Goal : numElts {[]} 1
    show numElts {[]} 1 from singleton_one_elt []
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ctble (seq_by_length A n)
    have h2 : A ×ₛ (seq_by_length A n) ∼ seq_by_length A (n + 1) :=
      Lemma_8_2_4_1 A n
    have h3 : ctble (A ×ₛ (seq_by_length A n)) := Theorem_8_2_1_1 h1 ih
    show ctble (seq_by_length A (n + 1)) from ctble_of_ctble_equinum h2 h3
    done
  done

lemma Lemma_8_2_4_3 {U : Type} (A : Set U) : ⋃₀ (sbl_set A) = seq A := by
  apply Set.ext
  fix l : List U
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ ⋃₀ (sbl_set A)
    define at h1
    obtain (S : Set (List U)) (h2 :  S ∈ sbl_set A ∧ l ∈ S) from h1
    have h3 : S ∈ sbl_set A := h2.left
    define at h3
    obtain (n : Nat) (h4 : seq_by_length A n = S) from h3
    have h5 : l ∈ S := h2.right
    rewrite [←h4] at h5
    define at h5
    show l ∈ seq A from h5.left
    done
  · -- (←)
    assume h1 : l ∈ seq A
    define
    set n : Nat := l.length
    apply Exists.intro (seq_by_length A n)
    apply And.intro
    · -- Proof of seq_by_length A n ∈ sbl_set A
      define
      apply Exists.intro n
      rfl
      done
    · -- Proof of l ∈ seq_by_length A n
      define
      apply And.intro h1
      rfl
      done
    done
  done

lemma Lemma_8_2_4_4 {U : Type} (A : Set U) : ctble (sbl_set A) := by
  rewrite [Theorem_8_1_5_2]
  apply Or.inr   --Goal : ∃ (f : Nat → Set (List U)), sbl_set A ⊆ range f
  apply Exists.intro (seq_by_length A)
  fix S : Set (List U)
  assume h1 : S ∈ sbl_set A
  define at h1; define
  show ∃ (x : Nat), seq_by_length A x = S from h1
  done

theorem Theorem_8_2_4 {U : Type} {A : Set U}
    (h1 : ctble A) : ctble (seq A) := by
  set F : Set (Set (List U)) := sbl_set A
  have h2 : ctble F := Lemma_8_2_4_4 A
  have h3 : ∀ S ∈ F, ctble S := by
    fix S : Set (List U)
    assume h3 : S ∈ F
    define at h3
    obtain (n : Nat) (h4 : seq_by_length A n = S) from h3
    rewrite [←h4]
    show ctble (seq_by_length A n) from Lemma_8_2_4_2 h1 n
    done
  rewrite [←Lemma_8_2_4_3 A]
  show ctble (⋃₀ sbl_set A) from Theorem_8_2_2 h2 h3
  done

theorem Cantor's_theorem : ¬ctble (Set Nat) := by
  by_contra h1
  rewrite [ctble_iff_set_nat_equinum] at h1
  obtain (J : Set Nat) (h2 : J ∼ Set Nat) from h1
  obtain (F : J → Set Nat) (h3 : one_to_one F ∧ onto F) from h2
  set f : Nat → Set Nat := func_extend F ∅
  set D : Set Nat := {n : Nat | n ∉ f n}
  obtain (nJ : J) (h4 : F nJ = D) from h3.right D
  set n : Nat := nJ.val
  have h5 : n ∈ D ↔ n ∉ f n := by rfl
  have h6 : f n = F nJ := fe_elt F ∅ nJ
  rewrite [h6, h4] at h5      --h5 : n ∈ D ↔ n ∉ D
  by_cases h7 : n ∈ D
  · -- Case 1. h7 : n ∈ D
    contradict h7
    show n ∉ D from h5.ltr h7
    done
  · -- Case 2. h7 : n ∉ D
    contradict h7
    show n ∈ D from h5.rtl h7
    done
  done

/- Section 8.3 -/
lemma csb_func_graph_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∈ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ f x = y := by
  apply Iff.intro
  · -- (→)
    assume h1 : (x, y) ∈ csb_func_graph f g X
    define at h1
    have h2 : ¬(x ∉ X ∧ g y = x) := by
      demorgan
      show x ∈ X ∨ g y ≠ x from Or.inl h
      done
    disj_syll h1 h2        --h1 : x ∈ X ∧ f x = y
    show f x = y from h1.right
    done
  · -- (←)
    assume h1 : f x = y
    define
    apply Or.inl
    show x ∈ X ∧ f x = y from And.intro h h1
    done
  done

lemma csb_func_graph_not_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∉ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ g y = x := sorry

lemma csb_func_graph_is_func_graph {U V : Type} {g : V → U} {X : Set U}
    (f : U → V) (h1 : ∀ (x : U), x ∉ X → x ∈ range g) (h2 : one_to_one g) :
    is_func_graph (csb_func_graph f g X) := by
  define
  fix x : U
  by_cases h3 : x ∈ X
  · -- Case 1. h3 : x ∈ X
    exists_unique
    · -- Existence
      apply Exists.intro (f x)
      rewrite [csb_func_graph_X f g h3]
      rfl
      done
    · -- Uniqueness
      fix y1 : V; fix y2 : V
      assume h4 : (x, y1) ∈ csb_func_graph f g X
      assume h5 : (x, y2) ∈ csb_func_graph f g X
      rewrite [csb_func_graph_X f g h3] at h4  --h4 : f x = y1
      rewrite [csb_func_graph_X f g h3] at h5  --h5 : f x = y2
      rewrite [←h4, ←h5]
      rfl
      done
    done
  · -- Case 2. h3 : x ∉ X
    exists_unique
    · -- Existence
      obtain (y : V) (h4 : g y = x) from h1 x h3
      apply Exists.intro y
      rewrite [csb_func_graph_not_X f g h3]
      show g y = x from h4
      done
    · -- Uniqueness
      fix y1 : V; fix y2 : V
      assume h4 : (x, y1) ∈ csb_func_graph f g X
      assume h5 : (x, y2) ∈ csb_func_graph f g X
      rewrite [csb_func_graph_not_X f g h3] at h4 --h4 : g y1 = x
      rewrite [csb_func_graph_not_X f g h3] at h5 --h5 : g y2 = x
      rewrite [←h5] at h4
      show y1 = y2 from h2 y1 y2 h4
      done
    done
  done

lemma csb_func_X
    {U V : Type} {f h : U → V} {g : V → U} {X : Set U} {x : U}
    (h1 : graph h = csb_func_graph f g X) (h2 : x ∈ X) : h x = f x := by
  rewrite [←graph_def, h1, csb_func_graph_X f g h2]
  rfl
  done

lemma csb_func_not_X
    {U V : Type} {f h : U → V} {g : V → U} {X : Set U} {x : U}
    (h1 : graph h = csb_func_graph f g X) (h2 : x ∉ X) : g (h x) = x := by
  have h3 : (x, h x) ∈ graph h := by rfl
  rewrite [h1, csb_func_graph_not_X f g h2] at h3
  show g (h x) = x from h3
  done

lemma csb_X_of_X
    {U V : Type} {f h : U → V} {g : V → U} {A0 : Set U} {x1 x2 : U}
    (h1 : graph h = csb_func_graph f g (cumul_image (g ∘ f) A0))
    (h2 : h x1 = h x2) (h3 : x1 ∈ cumul_image (g ∘ f) A0) :
    x2 ∈ cumul_image (g ∘ f) A0 := by
  by_contra h4                      --h4 : x2 ∉ cumul_image (g ∘ f) A0
  rewrite [csb_func_X h1 h3] at h2  --h2 : f x1 = h x2
  have h5 : (g ∘ f) x1 = x2 :=
    calc (g ∘ f) x1
      _ = g (f x1) := by rfl
      _ = g (h x2) := by rw [h2]
      _ = x2 := csb_func_not_X h1 h4
  obtain (n : Nat) (h6 : x1 ∈ rep_image (g ∘ f) n A0) from h3
  contradict h4               --Goal : x2 ∈ cumul_image (g ∘ f) A0
  apply Exists.intro (n + 1)  --Goal : x2 ∈ rep_image (g ∘ f) (n + 1) A0
  rewrite [rep_image_step]
  apply Exists.intro x1
  show x1 ∈ rep_image (g ∘ f) n A0 ∧ (g ∘ f) x1 = x2 from
    And.intro h6 h5
  done

theorem Cantor_Schroeder_Bernstein_theorem
    {U V : Type} {f : U → V} {g : V → U}
    (h1 : one_to_one f) (h2 : one_to_one g) : U ∼ V := by
  set A0 : Set U := {x : U | x ∉ range g}
  set X : Set U := cumul_image (g ∘ f) A0
  set H : Set (U × V) := csb_func_graph f g X
  have h3 : ∀ (x : U), x ∉ X → x ∈ range g := by
    fix x : U
    contrapos
    assume h3 : x ∉ range g
    define
    apply Exists.intro 0
    rewrite [rep_image_base]
    show x ∈ A0 from h3
    done
  have h4 : is_func_graph H := csb_func_graph_is_func_graph f h3 h2
  rewrite [←func_from_graph] at h4
  obtain (h : U → V) (h5 : graph h = H) from h4
  apply Exists.intro h
  apply And.intro
  · -- proof that h is one-to-one
    fix x1 : U; fix x2 : U
    assume h6 : h x1 = h x2
    by_cases h7 : x1 ∈ X
    · -- Case 1. h7 : x1 ∈ X
      have h8 : x2 ∈ X := csb_X_of_X h5 h6 h7
      rewrite [csb_func_X h5 h7, csb_func_X h5 h8] at h6 --h6 : f x1 = f x2
      show x1 = x2 from h1 x1 x2 h6
      done
    · -- Case 2. h7 : x1 ∉ X
      have h8 : x2 ∉ X := by
        contradict h7 with h8
        show x1 ∈ X from csb_X_of_X h5 h6.symm h8
        done
      show x1 = x2 from
        calc x1
          _ = g (h x1) := (csb_func_not_X h5 h7).symm
          _ = g (h x2) := by rw [h6]
          _ = x2 := csb_func_not_X h5 h8
      done
    done
  · -- proof that h is onto
    fix y : V
    by_cases h6 : g y ∈ X
    · -- Case 1. h6 : g y ∈ X
      define at h6
      obtain (n : Nat) (h7 : g y ∈ rep_image (g ∘ f) n A0) from h6
      have h8 : n ≠ 0 := by
        by_contra h8
        rewrite [h8, rep_image_base] at h7 --h7 : g y ∈ A0
        define at h7                       --h7 : ¬∃ (x : V), g x = g y
        contradict h7
        apply Exists.intro y
        rfl
        done
      obtain (k : Nat) (h9 : n = k + 1) from
        exists_eq_add_one_of_ne_zero h8
      rewrite [h9, rep_image_step] at h7
      obtain (x : U)
        (h10 : x ∈ rep_image (g ∘ f) k A0 ∧ (g ∘ f) x = g y) from h7
      have h11 : g (f x) = g y := h10.right
      have h12 : f x = y := h2 (f x) y h11
      have h13 : x ∈ X := Exists.intro k h10.left
      apply Exists.intro x
      rewrite [csb_func_X h5 h13]
      show f x = y from h12
      done
    · -- Case 2. h6 : g y ∉ X
      apply Exists.intro (g y)
      have h7 : g (h (g y)) = g y := csb_func_not_X h5 h6
      show h (g y) = y from h2 (h (g y)) y h7
      done
    done
  done
