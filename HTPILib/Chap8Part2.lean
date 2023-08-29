/- Copyright 2023 Daniel J. Velleman -/

import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Definiitons -/
def fnz (n : Nat) : Int := if 2 ∣ n then ↑(n / 2) else -↑((n + 1) / 2)

def fzn (a : Int) : Nat := if a ≥ 0 then 2 * Int.toNat a else 2 * Int.toNat (-a) - 1

def tri (k : Nat) : Nat := k * (k + 1) / 2

def fnnn (p : Nat × Nat) : Nat := tri (p.fst + p.snd) + p.fst

def num_elts_below (A : Set Nat) (m s : Nat) : Prop :=
  match m with
    | 0 => s = 0
    | n + 1 => (n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1)) ∨
                (n ∉ A ∧ num_elts_below A n s)

def enum (A : Set Nat) (s n : Nat) : Prop := n ∈ A ∧ num_elts_below A n s

def unique_val_on_N {U : Type} (R : Rel Nat U) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃x1 x2 : U⦄, R n x1 → R n x2 → x1 = x2

def nat_rel_onto {U : Type} (R : Rel Nat U) (A : Set U) : Prop :=
  ∀ ⦃x : U⦄, x ∈ A → ∃ (n : Nat), R n x

def fcnl_onto_from_nat {U : Type} (R : Rel Nat U) (A : Set U) : Prop :=
  unique_val_on_N R ∧ nat_rel_onto R A

def fcnl_one_one_to_nat {U : Type} (R : Rel U Nat) (A : Set U) : Prop :=
  fcnl_on R A ∧ ∀ ⦃x1 x2 : U⦄ ⦃n : Nat⦄,
    (x1 ∈ A ∧ R x1 n) → (x2 ∈ A ∧ R x2 n) → x1 = x2

def least_rel_to {U : Type} (S : Rel Nat U) (x : U) (n : Nat) : Prop :=
  S n x ∧ ∀ (m : Nat), S m x → n ≤ m

def restrict_to {U V : Type} (S : Rel U V) (A : Set U)
  (x : U) (y : V) : Prop := x ∈ A ∧ S x y

def fqn (q : Rat) : Nat := fnnn (fzn q.num, q.den)

def Set_rp_below (m : Nat) : Set Nat := { n : Nat | rel_prime m n ∧ n < m }

def Set_prod {U V : Type} (A : Set U) (B : Set V) : Set (U × V) :=
  { (a, b) : U × V | a ∈ A ∧ b ∈ B }

notation:75 A:75 " ×ₛ " B:75 => Set_prod A B

def Rel_prod {U V W X : Type} (R : Rel U V) (S : Rel W X)
  (p : U × W) (q : V × X) : Prop := R p.fst q.fst ∧ S p.snd q.snd

notation:75 R:75 " ×ᵣ " S:75 => Rel_prod R S

def qr (n a : Nat) : Nat × Nat := (a / n, a % n)

def mod_mod (m n a : Nat) : Nat × Nat := (a % m, a % n)

def enum_union_fam {U : Type}
  (F : Set (Set U)) (f : Set U → Rel Nat U) (R : Rel Nat (Set U))
  (n : Nat) (a : U) : Prop := ∃ (p : Nat × Nat), fnnn p = n ∧
    ∃ (A : Set U), A ∈ F ∧ R p.fst A ∧ (f A) p.snd a

def seq {U : Type} (A : Set U) : Set (List U) :=
  { l : List U | ∀ (x : U), x ∈ l → x ∈ A }

def seq_by_length {U : Type} (A : Set U) (n : Nat) : Set (List U) :=
  { l : List U | l ∈ seq A ∧ l.length = n }

def seq_cons (U : Type) (p : U × (List U)) : List U := p.fst :: p.snd

def sbl_set {U : Type} (A : Set U) : Set (Set (List U)) :=
  { S : Set (List U) | ∃ (n : Nat), seq_by_length A n = S }

def rep_common_image
  {U V : Type} (R S : Rel U V) (X0 : Set U) (n : Nat) : Set U :=
  match n with
    | 0 => X0
    | m + 1 => { a : U | ∃ (x : U),
                x ∈ rep_common_image R S X0 m ∧ ∃ (y : V), R x y ∧ S a y }

def cum_rep_image {U V : Type} (R S : Rel U V) (X0 : Set U) : Set U :=
  { a : U | ∃ (n : Nat), a ∈ rep_common_image R S X0 n }

def csb_match {U V : Type} (R S : Rel U V) (X0 : Set U)
  (x : U) (y : V) : Prop := x ∈ cum_rep_image R S X0 ∧ R x y ∨
    x ∉ cum_rep_image R S X0 ∧ S x y

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

lemma one_one_on_of_one_one {U V : Type} {f : U → V}
    (h : one_to_one f) (A : Set U) : one_one_on f A := by
  define
  fix x1 : U; fix x2 : U
  assume h1 : x1 ∈ A
  assume h2 : x2 ∈ A
  show f x1 = f x2 → x1 = x2 from h x1 x2
  done

lemma elt_Univ {U : Type} (u : U) :
    u ∈ Univ U := by trivial

theorem equinum_Univ {U V : Type} {f : U → V}
    (h1 : one_to_one f) (h2 : onto f) : Univ U ∼ Univ V := by
  have h3 : image f (Univ U) = Univ V := by
    apply Set.ext
    fix v : V
    apply Iff.intro
    · -- (→)
      assume h3 : v ∈ image f (Univ U)
      show v ∈ Univ V from elt_Univ v
      done
    · -- (←)
      assume h3 : v ∈ Univ V
      obtain (u : U) (h4 : f u = v) from h2 v
      apply Exists.intro u
      apply And.intro _ h4
      show u ∈ Univ U from elt_Univ u
      done
    done
  show Univ U ∼ Univ V from
    equinum_image (one_one_on_of_one_one h1 (Univ U)) h3
  done

theorem Z_equinum_N : Univ Int ∼ Univ Nat :=
  equinum_Univ fzn_one_one fzn_onto

theorem NxN_equinum_N : Univ (Nat × Nat) ∼ Univ Nat :=
  equinum_Univ fnnn_one_one fnnn_onto

lemma neb_step (A : Set Nat) (n s : Nat) : num_elts_below A (n + 1) s ↔
    (n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1)) ∨
      (n ∉ A ∧ num_elts_below A n s) := by rfl

lemma neb_step_elt {A : Set Nat} {n : Nat} (h1 : n ∈ A) (s : Nat) :
    num_elts_below A (n + 1) s ↔ 1 ≤ s ∧ num_elts_below A n (s - 1) := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h2 : n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1) ∨
      ¬n ∈ A ∧ num_elts_below A n s
    by_cases on h2
    · -- Case 1. h2 : n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1)
      show 1 ≤ s ∧ num_elts_below A n (s - 1) from h2.right
      done
    · -- Case 2. h2 : ¬n ∈ A ∧ num_elts_below A n s
      show 1 ≤ s ∧ num_elts_below A n (s - 1) from absurd h1 h2.left
      done
    done
  · -- (←)
    assume h2 : 1 ≤ s ∧ num_elts_below A n (s - 1)
    apply Or.inl
    show n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1) from And.intro h1 h2
    done
  done

lemma neb_step_not_elt {A : Set Nat} {n : Nat} (h1 : n ∉ A) (s : Nat) :
    num_elts_below A (n + 1) s ↔ num_elts_below A n s := by
  rewrite [neb_step]
  apply Iff.intro
  · -- (→)
    assume h2 : n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1) ∨
      ¬n ∈ A ∧ num_elts_below A n s
    by_cases on h2
    · -- Case 1. h2 : n ∈ A ∧ 1 ≤ s ∧ num_elts_below A n (s - 1)
      show num_elts_below A n s from absurd h2.left h1
      done
    · -- Case 2. h2 : ¬n ∈ A ∧ num_elts_below A n s
      show num_elts_below A n s from h2.right
      done
    done
  · -- (←)
    assume h2 : num_elts_below A n s
    apply Or.inr
    show ¬n ∈ A ∧ num_elts_below A n s from And.intro h1 h2
    done
  done

lemma neb_exists (A : Set Nat) :
    ∀ (n : Nat), ∃ (s : Nat), num_elts_below A n s := by
  by_induc
  · -- Base Case
    apply Exists.intro 0
    define
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∃ (s : Nat), num_elts_below A n s
    obtain (t : Nat) (h1 : num_elts_below A n t) from ih
    by_cases h2 : n ∈ A
    · -- Case 1. h2 : n ∈ A
      apply Exists.intro (t + 1)
      rewrite [neb_step_elt h2, Nat.add_sub_cancel]
      apply And.intro _ h1
      linarith
      done
    · -- Case 2. h2 : n ∉ A
      apply Exists.intro t
      rewrite [neb_step_not_elt h2]
      show num_elts_below A n t from h1
      done
    done
  done

lemma neb_unique (A : Set Nat) : ∀ ⦃n : Nat⦄, ∀ ⦃s1 s2 : Nat⦄,
    num_elts_below A n s1 → num_elts_below A n s2 → s1 = s2 := by
  by_induc
  · -- Base Case
    fix s1 : Nat; fix s2 : Nat
    assume h1 : num_elts_below A 0 s1
    assume h2 : num_elts_below A 0 s2
    define at h1; define at h2  --h1 : s1 = 0; h2 : s2 = 0
    rewrite [h1, h2]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ ⦃s1 s2 : Nat⦄,
      num_elts_below A n s1 → num_elts_below A n s2 → s1 = s2
    fix s1 : Nat; fix s2 : Nat
    assume h1 : num_elts_below A (n + 1) s1
    assume h2 : num_elts_below A (n + 1) s2
    by_cases h3 : n ∈ A
    · -- Case 1. h3 : n ∈ A
      rewrite [neb_step_elt h3] at h1
      rewrite [neb_step_elt h3] at h2
        --h1 : 1 ≤ s1 ∧ num_elts_below A n (s1 - 1)
        --h2 : 1 ≤ s1 ∧ num_elts_below A n (s1 - 1)
      have h4 : s1 - 1 = s2 - 1 := ih h1.right h2.right
      show s1 = s2 from
        calc s1
          _ = s1 - 1 + 1 := (Nat.sub_add_cancel h1.left).symm
          _ = s2 - 1 + 1 := by rw [h4]
          _ = s2 := Nat.sub_add_cancel h2.left
      done
    · -- Case 2. h3 : n ∉ A
      rewrite [neb_step_not_elt h3] at h1 --h1 : num_elts_below A n s1
      rewrite [neb_step_not_elt h3] at h2 --h2 : num_elts_below A n s2
      show s1 = s2 from ih h1 h2
      done
    done
  done

lemma neb_increase {A : Set Nat} {n s : Nat} (h1 : enum A s n) :
    ∀ ⦃m : Nat⦄, m ≥ n + 1 → ∀ ⦃t : Nat⦄, num_elts_below A m t → s < t := by
  by_induc
  · -- Base Case
    define at h1
    fix t : Nat
    assume h2 : num_elts_below A (n + 1) t
    rewrite [neb_step_elt h1.left] at h2
    have h3 : s = t - 1 := neb_unique A h1.right h2.right
    show s < t from
      calc s
        _ = t - 1 := h3
        _ < t - 1 + 1 := by linarith
        _ = t := Nat.sub_add_cancel h2.left
    done
  · -- Induction Step
    fix m : Nat
    assume h2 : m ≥ n + 1
    assume ih : ∀ ⦃t : Nat⦄, num_elts_below A m t → s < t
    fix t : Nat
    assume h3 : num_elts_below A (m + 1) t
    by_cases h4 : m ∈ A
    · -- Case 1. h4 : m ∈ A
      rewrite [neb_step_elt h4] at h3
      have h5 : s < t - 1 := ih h3.right
      show s < t from
        calc s
          _ < t - 1 := h5
          _ ≤ t := Nat.sub_le _ _
      done
    · -- Case 2. h4 : m ∉ A
      rewrite [neb_step_not_elt h4] at h3
      show s < t from ih h3
      done
    done
  done

lemma enum_not_skip {A : Set Nat} : ∀ ⦃m s : Nat⦄, num_elts_below A m s →
    ∀ t < s, ∃ (n : Nat), enum A t n := by
  by_induc
  · -- Base Case
    fix s : Nat
    assume h1 : num_elts_below A 0 s
    define at h1
    fix t : Nat
    contrapos
    assume h2 : ¬∃ (n : Nat), enum A t n
    linarith
    done
  · -- Induction Step
    fix m : Nat
    assume ih : ∀ ⦃s : Nat⦄, num_elts_below A m s → ∀ (t : Nat), t < s → ∃ (n : Nat), enum A t n
    fix s : Nat
    assume h1 : num_elts_below A (m + 1) s
    by_cases h2 : m ∈ A
    · -- Case 1. h2 : m ∈ A
      rewrite [neb_step_elt h2] at h1
      have h3 : ∀ (t : Nat), t < s - 1 → ∃ (n : Nat), enum A t n := ih h1.right
      fix t : Nat
      assume h4 : t < s
      by_cases h5 : t = s - 1
      · -- Case 1.1. h5 : t = s - 1
        apply Exists.intro m
        define
        apply And.intro h2
        rewrite [h5]
        show num_elts_below A m (s - 1) from h1.right
        done
      · -- Case 1.2. h5 : t ≠ s - 1
        have h6 : t ≤ s - 1 := Nat.le_pred_of_lt h4
        have h7 : t < s - 1 := Nat.lt_of_le_of_ne h6 h5
        show ∃ (n : Nat), enum A t n from ih h1.right t h7
        done
      done
    · -- Case 2. h2 : m ∉ A
      rewrite [neb_step_not_elt h2] at h1
      show ∀ (t : Nat), t < s → ∃ (n : Nat), enum A t n from ih h1
      done
    done
  done

lemma enum_le {A : Set Nat} {t n1 n2 : Nat}
    (h1 : enum A t n1) (h2 : enum A t n2) : n1 ≤ n2 := by
  by_contra h3
  have h4 : n2 + 1 ≤ n1 := by linarith
  define at h1
  have h5 : t < t := neb_increase h2 h4 h1.right
  linarith
  done

lemma enum_unique (A : Set Nat) (t : Nat) :
    ∀ ⦃n1 n2 : Nat⦄, enum A t n1 → enum A t n2 → n1 = n2 := by
  fix n1 : Nat; fix n2 : Nat
  assume h1 : enum A t n1
  assume h2 : enum A t n2
  have h3 : n1 ≤ n2 := enum_le h1 h2
  have h4 : n2 ≤ n1 := enum_le h2 h1
  linarith
  done

lemma inv_enum_fcnl (A : Set Nat) : fcnl_on (invRel (enum A)) A := by
  define
  fix n : Nat
  assume h1 : n ∈ A
  exists_unique
  · -- Existence
    obtain (s : Nat) (h2 : num_elts_below A n s) from neb_exists A n
    apply Exists.intro s
    define
    show n ∈ A ∧ num_elts_below A n s from And.intro h1 h2
    done
  · -- Uniqueness
    fix s1 : Nat; fix s2 : Nat
    assume h2 : invRel (enum A) n s1
    assume h3 : invRel (enum A) n s2
    define at h2; define at h3
    show s1 = s2 from neb_unique A h2.right h3.right
    done
  done

lemma bdd_subset_nat_match {A : Set Nat} {m s : Nat}
    (h1 : ∀ (n : Nat), n ∈ A → n < m) (h2 : num_elts_below A m s) :
    matching (enum A) (I s) A := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix t : Nat; fix n : Nat
    assume h3 : enum A t n
    have h4 : ∀ ⦃m : Nat⦄, m ≥ n + 1 → ∀ ⦃t_1 : Nat⦄, num_elts_below A m t_1 → t < t_1 :=
      neb_increase h3
    define at h3
    apply And.intro _ h3.left
    define
    have h5 : n < m := h1 n h3.left
    have h6 : m ≥ n + 1 := h5
    show t < s from h4 h6 h2
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- proof of fcnl_on (enum A) (I s)
      define
      fix t : Nat
      assume h3 : t ∈ I s
      define at h3
      exists_unique
      · -- Existence
        show ∃ (y : Nat), enum A t y from enum_not_skip h2 t h3
        done
      · -- Uniqueness
        show ∀ (y_1 y_2 : Nat), enum A t y_1 → enum A t y_2 → y_1 = y_2 from
          enum_unique A t
        done
      done
    · -- Proof of fcnl_on (invRel (enum A)) A
      show fcnl_on (invRel (enum A)) A from inv_enum_fcnl A
      done
    done
  done

lemma bdd_subset_nat {A : Set Nat} {m s : Nat}
    (h1 : ∀ (n : Nat), n ∈ A → n < m) (h2 : num_elts_below A m s) :
    I s ∼ A := Exists.intro (enum A) (bdd_subset_nat_match h1 h2)

lemma enum_fcnl_of_unbdd {A : Set Nat} (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ A ∧ n ≥ m) :
    fcnl_on (enum A) (Univ Nat) := by
  define
  by_induc
  · -- Base Case
    assume h2 : 0 ∈ Univ Nat
    exists_unique
    · -- Existence
      obtain (n : Nat) (h3 : n ∈ A ∧ n ≥0) from h1 0
      obtain (s : Nat) (h4 : num_elts_below A (n + 1) s) from neb_exists A (n + 1)
      have h5 : ∀ (t : Nat), t < s → ∃ (n : Nat), enum A t n := enum_not_skip h4
      rewrite [neb_step_elt h3.left] at h4
      show ∃ (y : Nat), enum A 0 y from h5 0 h4.left
      done
    · -- Uniqueness
      show ∀ (y_1 y_2 : Nat), enum A 0 y_1 → enum A 0 y_2 → y_1 = y_2 from enum_unique A 0
      done
    done
  · -- Induction Step
    fix s : Nat
    assume ih : s ∈ Univ Nat → ∃! (y : Nat), enum A s y
    assume h2 : s + 1 ∈ Univ Nat
    exists_unique
    · -- Existence
      have h3 : s ∈ Univ Nat := elt_Univ s
      obtain (m : Nat) (h4 : enum A s m)
        (h5 : ∀ (y_1 y_2 : Nat), enum A s y_1 → enum A s y_2 → y_1 = y_2) from ih h3
      obtain (n : Nat) (h6 : n ∈ A ∧ n ≥ m + 1) from h1 (m + 1)
      obtain (t : Nat) (h7 : num_elts_below A n t) from neb_exists A n
      have h8 : s < t := neb_increase h4 h6.right h7
      have h9 : s + 1 < t ∨ s + 1 = t := Nat.lt_or_eq_of_le h8
      by_cases on h9
      · -- Case 1. h9 : s + 1 < t
        show ∃ (y : Nat), enum A (s + 1) y from enum_not_skip h7 (s + 1) h9
        done
      · -- Case 2. h9 : s + 1 = t
        rewrite [h9]
        apply Exists.intro n
        define
        show n ∈ A ∧ num_elts_below A n t from And.intro h6.left h7
        done
      done
    · -- Uniqueness
      show ∀ (y_1 y_2 : Nat), enum A (s + 1) y_1 → enum A (s + 1) y_2 → y_1 = y_2
        from enum_unique A (s + 1)
      done
    done
  done

lemma unbdd_subset_nat_match {A : Set Nat}
    (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ A ∧ n ≥ m) :
    matching (enum A) (Univ Nat) A := by
  define
  apply And.intro
  · -- Proof of rel_within
    define
    fix s : Nat; fix n : Nat
    assume h2 : enum A s n
    define at h2
    apply And.intro (elt_Univ s) h2.left
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on (enum A)
      show fcnl_on (enum A) (Univ Nat) from enum_fcnl_of_unbdd h1
      done
    · -- Proof of fcnl_on (invRel (enum A))
      show fcnl_on (invRel (enum A)) A from inv_enum_fcnl A
      done
    done
  done

lemma unbdd_subset_nat {A : Set Nat}
    (h1 : ∀ (m : Nat), ∃ (n : Nat), n ∈ A ∧ n ≥ m) :
    denum A := Exists.intro (enum A) (unbdd_subset_nat_match h1)

lemma subset_nat_ctble (A : Set Nat) : ctble A := by
  define          --Goal : finite A ∨ denum A
  by_cases h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ A → n < m
  · -- Case 1. h1 : ∃ (m : Nat), ∀ (n : Nat), n ∈ A → n < m
    apply Or.inl  --Goal : finite A
    obtain (m : Nat) (h2 : ∀ (n : Nat), n ∈ A → n < m) from h1
    obtain (s : Nat) (h3 : num_elts_below A m s) from neb_exists A m
    apply Exists.intro s
    show I s ∼ A from bdd_subset_nat h2 h3
    done
  · -- Case 2. h1 : ¬∃ (m : Nat), ∀ (n : Nat), n ∈ A → n < m
    apply Or.inr  --Goal : denum A
    push_neg at h1
      --This tactic converts h1 to ∀ (m : Nat), ∃ (n : Nat), n ∈ A ∧ m ≤ n
    show denum A from unbdd_subset_nat h1
    done
  done

lemma ctble_of_equinum_ctble {U V : Type} {A : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : ctble A) : ctble B := sorry

lemma ctble_iff_equinum_set_nat {U : Type} (A : Set U) : 
    ctble A ↔ ∃ (I : Set Nat), I ∼ A := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble A
    define at h1  --h1 : finite A ∨ denum A
    by_cases on h1
    · -- Case 1. h1 : finite A
      define at h1  --h1 : ∃ (n : Nat), I n ∼ A
      obtain (n : Nat) (h2 : I n ∼ A) from h1
      show ∃ (I : Set Nat), I ∼ A from Exists.intro (I n) h2
      done
    · -- Case 2. h1 : denum A
      rewrite [denum_def] at h1  --h1 : Univ Nat ∼ A
      show ∃ (I : Set Nat), I ∼ A from Exists.intro (Univ Nat) h1
      done
    done
  · -- (←)
    assume h1 : ∃ (I : Set Nat), I ∼ A
    obtain (I : Set Nat) (h2 : I ∼ A) from h1
    have h3 : ctble I := subset_nat_ctble I
    show ctble A from ctble_of_equinum_ctble h2 h3
    done
  done

theorem Theorem_8_1_5_1_to_2 {U : Type} {A : Set U} (h1 : ctble A) :
    ∃ (R : Rel Nat U), fcnl_onto_from_nat R A := by
  rewrite [ctble_iff_equinum_set_nat] at h1
  obtain (I : Set Nat) (h2 : I ∼ A) from h1
  obtain (R : Rel Nat U) (h3 : matching R I A) from h2
  define at h3
    --h3 : rel_within R I A ∧ fcnl_on R I ∧ fcnl_on (invRel R) A
  apply Exists.intro R
  define  --Goal : unique_val_on_N R ∧ nat_rel_onto R A
  apply And.intro
  · -- Proof of unique_val_on_N R
    define
    fix n : Nat; fix x1 : U; fix x2 : U
    assume h4 : R n x1
    assume h5 : R n x2      --Goal : x1 = x2
    have h6 : n ∈ I ∧ x1 ∈ A := h3.left h4
    show x1 = x2 from fcnl_unique h3.right.left h6.left h4 h5
    done
  · -- Proof of nat_rel_onto R A
    define
    fix x : U
    assume h4 : x ∈ A  --Goal : ∃ (n : Nat), R n x
    show ∃ (n : Nat), R n x from fcnl_exists h3.right.right h4
    done
  done

lemma exists_least_rel_to {U : Type} {S : Rel Nat U} {x : U}
    (h1 : ∃ (n : Nat), S n x) : ∃ (n : Nat), least_rel_to S x n := by
  set W : Set Nat := { n : Nat | S n x }
  have h2 : ∃ (n : Nat), n ∈ W := h1
  show ∃ (n : Nat), least_rel_to S x n from well_ord_princ W h2
  done

theorem Theorem_8_1_5_2_to_3 {U : Type} {A : Set U}
    (h1 : ∃ (R : Rel Nat U), fcnl_onto_from_nat R A) :
    ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A := by
  obtain (S : Rel Nat U) (h2 : fcnl_onto_from_nat S A) from h1
  define at h2  --h2 : unique_val_on_N S ∧ nat_rel_onto S A
  set R : Rel U Nat := least_rel_to S
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of fcnl_on R A
    define
    fix x : U
    assume h4 : x ∈ A  --Goal : ∃! (y : Nat), R x y
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
    fix x1 : U; fix x2 : U; fix n : Nat
    assume h4 : x1 ∈ A ∧ R x1 n
    assume h5 : x2 ∈ A ∧ R x2 n
    have h6 : R x1 n := h4.right
    have h7 : R x2 n := h5.right
    define at h6   --h6 : S n x1 ∧ ∀ (m : Nat), S m x1 → n ≤ m
    define at h7   --h7 : S n x2 ∧ ∀ (m : Nat), S m x2 → n ≤ m
    show x1 = x2 from h2.left h6.left h7.left
    done
  done

theorem Theorem_8_1_5_3_to_1 {U : Type} {A : Set U}
    (h1 : ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A) :
    ctble A := by
  obtain (S : Rel U Nat) (h2 : fcnl_one_one_to_nat S A) from h1
  define at h2  --h2 : fcnl_on S A ∧ ∀ ⦃x1 x2 : U⦄ ⦃n : Nat⦄,
                --x1 ∈ A ∧ S x1 n → x2 ∈ A ∧ S x2 n → x1 = x2
  rewrite [ctble_iff_equinum_set_nat]  --Goal : ∃ (I : Set Nat), I ∼ A
  set R : Rel Nat U := invRel (restrict_to S A)
  set I : Set Nat := { n : Nat | ∃ (x : U), R n x }
  apply Exists.intro I
  define        --Goal : ∃ (R : Rel Nat U), matching R I A
  apply Exists.intro R
  define
  apply And.intro
  · -- Proof of rel_within R I A
    define
    fix n : Nat; fix x : U
    assume h3 : R n x   --Goal : n ∈ I ∧ x ∈ A
    apply And.intro
    · -- Proof that n ∈ I
      define            --Goal : ∃ (x : U), R n x
      show ∃ (x : U), R n x from Exists.intro x h3
      done
    · -- Proof that x ∈ A
      define at h3      --h3 : x ∈ A ∧ S x n
      show x ∈ A from h3.left
      done
    done
  · -- Proofs of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on R I
      define
      fix n : Nat
      assume h3 : n ∈ I   --Goal : ∃! (y : U), R n y
      exists_unique
      · -- Existence
        define at h3      --h3 : ∃ (x : U), R n x
        show ∃ (y : U), R n y from h3
        done
      · -- Uniqueness
        fix x1 : U; fix x2 : U
        assume h4 : R n x1
        assume h5 : R n x2
        define at h4      --h4 : x1 ∈ A ∧ S x1 n; 
        define at h5      --h5 : x2 ∈ A ∧ S x2 n
        show x1 = x2 from h2.right h4 h5
        done
      done
    · -- Proof of fcnl_on (invRel R) A
      define
      fix x : U
      assume h3 : x ∈ A  --Goal : ∃! (y : Nat), invRel R x y
      exists_unique
      · -- Existence
        obtain (y : Nat) (h4 : S x y) from fcnl_exists h2.left h3
        apply Exists.intro y
        define
        show x ∈ A ∧ S x y from And.intro h3 h4
        done
      · -- Uniqueness
        fix n1 : Nat; fix n2 : Nat
        assume h4 : invRel R x n1
        assume h5 : invRel R x n2  --Goal : n1 = n2
        define at h4     --h4 : x ∈ A ∧ S x n1
        define at h5     --h5 : x ∈ A ∧ S x n2
        show n1 = n2 from fcnl_unique h2.left h3 h4.right h5.right
        done
      done
    done
  done

theorem Theorem_8_1_5_2 {U : Type} (A : Set U) :
    ctble A ↔ ∃ (R : Rel Nat U), fcnl_onto_from_nat R A := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble A
    show ∃ (R : Rel Nat U), fcnl_onto_from_nat R A from
      Theorem_8_1_5_1_to_2 h1
    done
  · -- (←)
    assume h1 : ∃ (R : Rel Nat U), fcnl_onto_from_nat R A
    have h2 : ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A :=
      Theorem_8_1_5_2_to_3 h1
    show ctble A from Theorem_8_1_5_3_to_1 h2
    done
  done

theorem Theorem_8_1_5_3 {U : Type} (A : Set U) :
    ctble A ↔ ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A := by
  apply Iff.intro
  · -- (→)
    assume h1 : ctble A
    have h2 : ∃ (R : Rel Nat U), fcnl_onto_from_nat R A :=
      Theorem_8_1_5_1_to_2 h1
    show ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A from
      Theorem_8_1_5_2_to_3 h2
    done
  · -- (←)
    assume h1 : ∃ (R : Rel U Nat), fcnl_one_one_to_nat R A
    show ctble A from Theorem_8_1_5_3_to_1 h1
    done
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

theorem numElts_unique {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := by
  rewrite [numElts_def] at h1      --h1 : I m ∼ A
  rewrite [numElts_def] at h2      --h2 : I n ∼ A
  have h3 : A ∼ I n := Theorem_8_1_3_2 h2
  have h4 : I m ∼ I n := Theorem_8_1_3_3 h1 h3
  show m = n from eq_of_I_equinum h4
  done

lemma Set_rp_below_def (a m : Nat) :
    a ∈ Set_rp_below m ↔ rel_prime m a ∧ a < m := by rfl

lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (Set_rp_below m) k (num_rp_below m k) := sorry

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

lemma Set_prod_def {U V : Type} (A : Set U) (B : Set V) (a : U) (b : V) :
    (a, b) ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B := by rfl

lemma Rel_prod_def {U V W X : Type} (R : Rel U V) (S : Rel W X)
    (u : U) (v : V) (w : W) (x : X) :
    (R ×ᵣ S) (u, w) (v, x) ↔ R u v ∧ S w x := by rfl

lemma prod_match {U V W X : Type}
    {A : Set U} {B : Set V} {C : Set W} {D : Set X}
    {R : Rel U V} {S : Rel W X}
    (h1 : matching R A B) (h2 : matching S C D) :
    matching (R ×ᵣ S) (A ×ₛ C) (B ×ₛ D) := sorry

theorem Theorem_8_1_2_1
    {U V W X : Type} {A : Set U} {B : Set V} {C : Set W} {D : Set X}
    (h1 : A ∼ B) (h2 : C ∼ D) : A ×ₛ C ∼ B ×ₛ D := by
  obtain (R : Rel U V) (h3 : matching R A B) from h1
  obtain (S : Rel W X) (h4 : matching S C D) from h2
  apply Exists.intro (R ×ᵣ S)
  show matching (R ×ᵣ S) (A ×ₛ C) (B ×ₛ D) from prod_match h3 h4
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
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

lemma I_prod (m n : Nat) : I (m * n) ∼ I m ×ₛ I n := equinum_image
  (one_one_on_of_one_one (qr_one_one n) (I (m * n))) (qr_image m n)

theorem numElts_prod {U V : Type} {A : Set U} {B : Set V} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts B n) : numElts (A ×ₛ B) (m * n) := by
  rewrite [numElts_def] at h1     --h1 : I m ∼ A
  rewrite [numElts_def] at h2     --h2 : I n ∼ B
  rewrite [numElts_def]           --Goal : I (m * n) ∼ A ×ₛ B
  have h3 : I m ×ₛ I n ∼ A ×ₛ B := Theorem_8_1_2_1 h1 h2
  have h4 : I (m * n) ∼ I m ×ₛ I n := I_prod m n
  show I (m * n) ∼ A ×ₛ B from Theorem_8_1_3_3 h4 h3
  done

lemma mod_mod_def (m n a : Nat) : mod_mod m n a = (a % m, a % n) := by rfl

--From exercises of Section 7.3
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

/- Stated in Chap7.lean
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry
-/

--From exercises of Section 7.4
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
  rewrite [←congr_iff_mod_eq_Nat, ←congr_iff_mod_eq_Nat] at h5
      --h5 : ↑a1 ≡ ↑a2 (MOD m) ∧ ↑a1 ≡ ↑a2 (MOD n)
  rewrite [←Lemma_7_4_5 _ _ h1] at h5  --h5 : ↑a1 ≡ ↑a2 (MOD m * n)
  rewrite [congr_iff_mod_eq_Nat] at h5     --h5 : a1 % (m * n) = a2 % (m * n)
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
      rewrite [congr_iff_mod_eq_Nat, congr_iff_mod_eq_Nat] at h5
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

lemma eq_numElts_of_equinum {U V : Type} {A : Set U} {B : Set V} {n : Nat}
    (h1 : A ∼ B) (h2 : numElts A n) : numElts B n := by
  rewrite [numElts_def] at h2   --h2 : I n ∼ A
  rewrite [numElts_def]         --Goal : I n ∼ B
  show I n ∼ B from Theorem_8_1_3_3 h2 h1
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
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

theorem Theorem_8_2_1_1 {U V : Type} {A : Set U} {B : Set V}
    (h1 : ctble A) (h2 : ctble B) : ctble (A ×ₛ B) := by
  rewrite [ctble_iff_equinum_set_nat] at h1
  rewrite [ctble_iff_equinum_set_nat] at h2
  obtain (I : Set Nat) (h3 : I ∼ A) from h1
  obtain (J : Set Nat) (h4 : J ∼ B) from h2
  have h5 : I ×ₛ J ∼ A ×ₛ B := Theorem_8_1_2_1 h3 h4
  have h6 : I ×ₛ J ⊆ Univ (Nat × Nat) := by
    fix p : Nat × Nat
    assume h6 : p ∈ I ×ₛ J
    show p ∈ Univ (Nat × Nat) from elt_Univ p
    done
  have h7 : ctble (Univ (Nat × Nat)) := by
    define   --Goal : finite (Univ (Nat × Nat)) ∨ denum (Univ (Nat × Nat))
    apply Or.inr
    rewrite [denum_def]
    show Univ Nat ∼ Univ (Nat × Nat) from Theorem_8_1_3_2 NxN_equinum_N
    done
  have h8 : ctble (I ×ₛ J) := Exercise_8_1_17 h6 h7
  show ctble (A ×ₛ B) from ctble_of_equinum_ctble h5 h8
  done

lemma Lemma_8_2_2_1 {U : Type} {F : Set (Set U)} {f : Set U → Rel Nat U}
    (h1 : ctble F) (h2 : ∀ A ∈ F, fcnl_onto_from_nat (f A) A) :
    ctble (⋃₀ F) := by
  rewrite [Theorem_8_1_5_2] at h1
  rewrite [Theorem_8_1_5_2]
  obtain (R : Rel Nat (Set U)) (h3 : fcnl_onto_from_nat R F) from h1
  define at h3
  have Runiqueval : unique_val_on_N R := h3.left
  have Ronto : nat_rel_onto R F := h3.right
  set S : Rel Nat U := enum_union_fam F f R
  apply Exists.intro S
  define
  apply And.intro
  · -- Proof of unique_val_on_N S
    define
    fix n : Nat; fix a1 : U; fix a2 : U
    assume Sna1 : S n a1
    assume Sna2 : S n a2         --Goal : a1 = a2
    define at Sna1; define at Sna2
    obtain ((i1, j1) : Nat × Nat) (h4 : fnnn (i1, j1) = n ∧
      ∃ (A : Set U), A ∈ F ∧ R i1 A ∧ f A j1 a1) from Sna1
    obtain (A1 : Set U) (Aija1 : A1 ∈ F ∧ R i1 A1 ∧ f A1 j1 a1)
      from h4.right
    obtain ((i2, j2) : Nat × Nat) (h5 : fnnn (i2, j2) = n ∧
      ∃ (A : Set U), A ∈ F ∧ R i2 A ∧ f A j2 a2) from Sna2
    obtain (A2 : Set U) (Aija2 : A2 ∈ F ∧ R i2 A2 ∧ f A2 j2 a2)
      from h5.right
    rewrite [←h5.left] at h4
    have h6 : (i1, j1) = (i2, j2) :=
      fnnn_one_one (i1, j1) (i2, j2) h4.left
    have h7 : i1 = i2 ∧ j1 = j2 := Prod.mk.inj h6
    rewrite [h7.left, h7.right] at Aija1
      --Aija1 : A1 ∈ F ∧ R i2 A1 ∧ f A1 j2 a1
    define at Runiqueval
    have h8 : A1 = A2 := Runiqueval Aija1.right.left Aija2.right.left
    rewrite [h8] at Aija1       --Aija1 : A2 ∈ F ∧ R i2 A2 ∧ f A2 j2 a1
    have fA2fcnlonto : fcnl_onto_from_nat (f A2) A2 := h2 A2 Aija2.left
    define at fA2fcnlonto
    have fA2uniqueval : unique_val_on_N (f A2) := fA2fcnlonto.left
    define at fA2uniqueval
    show a1 = a2 from fA2uniqueval Aija1.right.right Aija2.right.right
    done
  · -- Proof of nat_rel_onto S (⋃₀ F)
    define
    fix x : U
    assume h4 : x ∈ ⋃₀ F    --Goal : ∃ (n : Nat), S n x
    define at h4
    obtain (A : Set U) (h5 : A ∈ F ∧ x ∈ A) from h4
    define at Ronto
    obtain (i : Nat) (h6 : R i A) from Ronto h5.left
    have fAfcnlonto : fcnl_onto_from_nat (f A) A := h2 A h5.left
    define at fAfcnlonto
    have fAonto : nat_rel_onto (f A) A := fAfcnlonto.right
    define at fAonto
    obtain (j : Nat) (h7 : f A j x) from fAonto h5.right
    apply Exists.intro (fnnn (i, j))
    define    --Goal : ∃ (p : Nat × Nat), fnnn p = fnnn (i, j) ∧
              --       ∃ (A : Set U), A ∈ F ∧ R p.fst A ∧ f A p.snd x
    apply Exists.intro (i, j)
    apply And.intro
    · -- Proof that fnnn (i, j) = fnnn (i, j)
      rfl
      done
    · -- Proof that ∃ (A : Set U), A ∈ F ∧
      --            R (i, j).fst A ∧ f A (i, j).snd x
      apply Exists.intro A
      show A ∈ F ∧ R (i, j).fst A ∧ f A (i, j).snd x from
        And.intro h5.left (And.intro h6 h7)
      done
    done
  done

lemma Lemma_8_2_2_2 {U : Type} {F : Set (Set U)} (h : ∀ A ∈ F, ctble A) :
    ∃ (f : Set U → Rel Nat U), ∀ A ∈ F, fcnl_onto_from_nat (f A) A := by
  have h1 : ∀ (A : Set U), ∃ (SA : Rel Nat U),
      A ∈ F → fcnl_onto_from_nat SA A := by
    fix A : Set U
    by_cases h2 : A ∈ F
    · -- Case 1. h2 : A ∈ F
      have h3 : ctble A := h A h2
      rewrite [Theorem_8_1_5_2] at h3
      obtain (SA : Rel Nat U) (h4 : fcnl_onto_from_nat SA A) from h3
      apply Exists.intro SA
      assume h5 : A ∈ F
      show fcnl_onto_from_nat SA A from h4
      done
    · -- Case 2. h2 : A ∉ F
      apply Exists.intro (emptyRel Nat U)
      assume h3 : A ∈ F
      show fcnl_onto_from_nat (emptyRel Nat U) A from absurd h3 h2
      done
    done
  set f : Set U → Rel Nat U := fun (A : Set U) => Classical.choose (h1 A)
  apply Exists.intro f
  fix A : Set U
  show A ∈ F → fcnl_onto_from_nat (f A) A from Classical.choose_spec (h1 A)
  done

theorem Theorem_8_2_2 {U : Type} {F : Set (Set U)}
    (h1 : ctble F) (h2 : ∀ A ∈ F, ctble A) : ctble (⋃₀ F) := by
  obtain (f : Set U → Rel Nat U) (h3 : ∀ (A : Set U), A ∈ F →
    fcnl_onto_from_nat (f A) A) from Lemma_8_2_2_2 h2
  show ctble (⋃₀ F) from Lemma_8_2_2_1 h1 h3
  done

lemma seq_def {U : Type} (A : Set U) (l : List U) :
    l ∈ seq A ↔ ∀ (x : U), x ∈ l → x ∈ A := by rfl

lemma sbl_base {U : Type} (A : Set U) : seq_by_length A 0 = {[]} := by
  apply Set.ext
  fix l : List U
  apply Iff.intro
  · -- (→)
    assume h1 : l ∈ seq_by_length A 0
    define at h1   --h1 : l ∈ seq A ∧ List.length l = 0
    rewrite [List.length_eq_zero] at h1
    define
    show l = [] from h1.right
    done
  · -- (←)
    assume h1 : l ∈ {[]}
    define at h1     --h1 : l = []
    define           --Goal : l ∈ seq A ∧ List.length l = 0
    apply And.intro _ (List.length_eq_zero.rtl h1)
    define           --Goal : ∀ (x : U), x ∈ l → x ∈ A
    fix x : U
    assume h2 : x ∈ l
    contradict h2 with h3
    rewrite [h1]
    show ¬x ∈ [] from List.not_mem_nil x
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
    A ×ₛ (seq_by_length A n) ∼ seq_by_length A (n + 1) :=
  equinum_image (one_one_on_of_one_one (seq_cons_one_one U)
    (A ×ₛ (seq_by_length A n))) (seq_cons_image A n)

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
    show ctble (seq_by_length A (n + 1)) from ctble_of_equinum_ctble h2 h3
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

theorem ctble_of_onto_func_from_N {U : Type} {A : Set U} {f : Nat → U}
    (h1 : ∀ x ∈ A, ∃ (n : Nat), f n = x) : ctble A := sorry

lemma Lemma_8_2_4_4 {U : Type} (A : Set U) : ctble (sbl_set A) := by
  have h1 : ∀ S ∈ sbl_set A, ∃ (n : Nat), seq_by_length A n = S := by
    fix S : Set (List U)
    assume h1 : S ∈ sbl_set A
    define at h1
    show ∃ (n : Nat), seq_by_length A n = S from h1
    done
  show ctble (sbl_set A) from ctble_of_onto_func_from_N h1
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

theorem Cantor's_theorem : ¬ctble (Univ (Set Nat)) := by
  by_contra h1
  rewrite [Theorem_8_1_5_2] at h1
  obtain (R : Rel Nat (Set Nat))
    (h2 : fcnl_onto_from_nat R (Univ (Set Nat))) from h1
  define at h2
  have h3 : unique_val_on_N R := h2.left
  have h4 : nat_rel_onto R (Univ (Set Nat)) := h2.right
  set D : Set Nat := { n : Nat | ∃ (X : Set Nat), R n X ∧ n ∉ X }
  have h5 : D ∈ Univ (Set Nat) := elt_Univ D
  define at h4
  obtain (n : Nat) (h6 : R n D) from h4 h5
  by_cases h7 : n ∈ D
  · -- Case 1. h7 : n ∈ D
    contradict h7
    define at h7
    obtain (X : Set Nat) (h8 : R n X ∧ ¬n ∈ X) from h7
    define at h3
    have h9 : D = X := h3 h6 h8.left
    rewrite [h9]
    show ¬n ∈ X from h8.right
    done
  · -- Case 2. h7 : n ∉ D
    contradict h7
    define
    show ∃ (X : Set Nat), R n X ∧ ¬n ∈ X from
      Exists.intro D (And.intro h6 h7)
    done
  done

/- Section 8.3 -/
lemma rep_common_image_step
    {U V : Type} (R S : Rel U V) (X0 : Set U) (m : Nat) (a : U) :
    a ∈ rep_common_image R S X0 (m + 1) ↔ ∃ (x : U),
      x ∈ rep_common_image R S X0 m ∧ ∃ (y : V), R x y ∧ S a y := by rfl

lemma csb_match_cri {U V : Type} {R S : Rel U V} {X0 : Set U}
    {x : U} {y : V} (h1 : csb_match R S X0 x y)
    (h2 : x ∈ cum_rep_image R S X0) : R x y := by
  by_cases on h1
  · -- Case 1. h1 : x ∈ cum_rep_image R S X0 ∧ R x y
    show R x y from h1.right
    done
  · -- Case 2. h1 : ¬x ∈ cum_rep_image R S X0 ∧ S x y
    show R x y from absurd h2 h1.left
    done
  done

lemma csb_match_not_cri {U V : Type} {R S : Rel U V} {X0 : Set U}
    {x : U} {y : V} (h1 : csb_match R S X0 x y)
    (h2 : x ∉ cum_rep_image R S X0) : S x y := by
  by_cases on h1
  · -- Case 1. h1 : x ∈ cum_rep_image R S X0 ∧ R x y
    show S x y from absurd h1.left h2
    done
  · -- Case 2. h1 : ¬x ∈ cum_rep_image R S X0 ∧ S x y
    show S x y from h1.right
    done
  done

lemma csb_cri_of_cri
    {U V : Type} {R S : Rel U V} {X0 : Set U} {x1 x2 : U} {y : V}
    (h1 : csb_match R S X0 x1 y) (h2 : csb_match R S X0 x2 y)
    (h3 : x1 ∈ cum_rep_image R S X0) : x2 ∈ cum_rep_image R S X0 := by
  have h4 : R x1 y := csb_match_cri h1 h3
  by_contra h5
  have h6 : S x2 y := csb_match_not_cri h2 h5
  contradict h5       --Goal : x2 ∈ cum_rep_image R S X0
  define at h3
  define
  obtain (n : Nat) (h7 : x1 ∈ rep_common_image R S X0 n) from h3
  apply Exists.intro (n + 1)  --Goal : x2 ∈ rep_common_image R S X0 (n + 1)
  rewrite [rep_common_image_step]
  apply Exists.intro x1
    --Goal : x1 ∈ rep_common_image R S X0 n ∧ ∃ (y : V), R x1 y ∧ S x2 y
  apply And.intro h7
  show ∃ (y : V), R x1 y ∧ S x2 y from Exists.intro y (And.intro h4 h6)
  done

theorem Cantor_Schroeder_Bernstein_theorem
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : C ⊆ A) (h2 : D ⊆ B) (h3 : A ∼ D) (h4 : C ∼ B) : A ∼ B := by
  obtain (R : Rel U V) (R_match_AD : matching R A D) from h3
  obtain (S : Rel U V) (S_match_CB : matching S C B) from h4
  define at R_match_AD; define at S_match_CB
  set X0 : Set U := A \ C
  set X : Set U := cum_rep_image R S X0
  set T : Rel U V := csb_match R S X0
  have Tdef : ∀ (x : U) (y : V),
      T x y ↔ (x ∈ X ∧ R x y) ∨ (x ∉ X ∧ S x y) := by
    fix x : U; fix y : V
    rfl
    done
  have A_not_X_in_C : A \ X ⊆ C := by
    fix a : U
    assume h5 : a ∈ A \ X
    contradict h5.right with h6  --h6 : ¬a ∈ C;  Goal : a ∈ X
    define  --Goal : ∃ (n : Nat), a ∈ rep_common_image R S X0 n
    apply Exists.intro 0 
    define
    show a ∈ A ∧ ¬a ∈ C from And.intro h5.left h6
    done
  define    --Goal : ∃ (R : Rel U V), matching R A B
  apply Exists.intro T
  define    --Goal : rel_within T A B ∧ fcnl_on T A ∧ fcnl_on (invRel T) B
  apply And.intro
  · -- Proof of rel_within T A B
    define
    fix a : U; fix b : V
    assume h5 : T a b
    rewrite [Tdef] at h5   --h5 : a ∈ X ∧ R a b ∨ ¬a ∈ X ∧ S a b
    by_cases on h5
    · -- Case 1. h5 : a ∈ X ∧ R a b
      have h6 : a ∈ A ∧ b ∈ D := R_match_AD.left h5.right
      show a ∈ A ∧ b ∈ B from And.intro h6.left (h2 h6.right)
      done
    · -- Case 2. h5 : a ∉ X ∧ S a b
      have h6 : a ∈ C ∧ b ∈ B := S_match_CB.left h5.right
      show a ∈ A ∧ b ∈ B from And.intro (h1 h6.left) h6.right
      done
    done
  · -- Proof of fcnl_ons
    apply And.intro
    · -- Proof of fcnl_on T A
      define
      fix a : U
      assume aA : a ∈ A   --Goal : ∃! (y : V), T a y
      exists_unique
      · -- Existence
        by_cases h5 : a ∈ X
        · -- Case 1. h5 : a ∈ X
          obtain (b : V) (Rab : R a b) from
            fcnl_exists R_match_AD.right.left aA
          apply Exists.intro b
          rewrite [Tdef]
          show a ∈ X ∧ R a b ∨ ¬a ∈ X ∧ S a b from
            Or.inl (And.intro h5 Rab)
          done
        · -- Case 2. h5 : a ∉ X
          have aC : a ∈ C := A_not_X_in_C (And.intro aA h5)
          obtain (b : V) (Sab : S a b) from
            fcnl_exists S_match_CB.right.left aC
          apply Exists.intro b
          rewrite [Tdef]
          show a ∈ X ∧ R a b ∨ ¬a ∈ X ∧ S a b from
            Or.inr (And.intro h5 Sab)
          done
        done
      · -- Uniqueness
        fix b1 : V; fix b2 : V
        assume Tab1 : T a b1
        assume Tab2 : T a b2
        by_cases h5 : a ∈ X
        · -- Case 1. h5 : a ∈ X
          have Rab1 : R a b1 := csb_match_cri Tab1 h5
          have Rab2 : R a b2 := csb_match_cri Tab2 h5
          show b1 = b2 from
            fcnl_unique R_match_AD.right.left aA Rab1 Rab2
          done
        · -- Case 2. h5 : ¬a ∈ X
          have Sab1 : S a b1 := csb_match_not_cri Tab1 h5
          have Sab2 : S a b2 := csb_match_not_cri Tab2 h5
          have aC : a ∈ C := A_not_X_in_C (And.intro aA h5)
          show b1 = b2 from
            fcnl_unique S_match_CB.right.left aC Sab1 Sab2
          done
        done
      done
    · -- Proof of fcnl_on (invRel T) B
      define
      fix b : V
      assume bB : b ∈ B
      obtain (c : U) (Scb : S c b) from
        fcnl_exists S_match_CB.right.right bB
      have cC : c ∈ C := (S_match_CB.left Scb).left
      exists_unique
      · -- Existence
        by_cases h5 : c ∈ X
        · -- Case 1. h5 : c ∈ X
          define at h5
          obtain (n : Nat) (h6 : c ∈ rep_common_image R S X0 n) from h5
          have h7 : n ≠ 0 := by
            by_contra h7
            rewrite [h7] at h6
            define at h6       --h6 : c ∈ A ∧ ¬c ∈ C
            show False from h6.right cC
            done
          obtain (m : Nat) (h8 : n = m + 1) from
            exists_eq_add_one_of_ne_zero h7
          rewrite [h8] at h6
          rewrite [rep_common_image_step] at h6
          obtain (a : U) (h9 : a ∈ rep_common_image R S X0 m ∧
            ∃ (y : V), R a y ∧ S c y) from h6
          apply Exists.intro a
          rewrite [invRel_def, Tdef]
          apply Or.inl    --Goal : a ∈ X ∧ R a b
          obtain (y : V) (h10 : R a y ∧ S c y) from h9.right
          have h11 : y = b :=
            fcnl_unique S_match_CB.right.left cC h10.right Scb
          rewrite [h11] at h10
          apply And.intro _ h10.left
          define
          show ∃ (n : Nat), a ∈ rep_common_image R S X0 n from
            Exists.intro m h9.left
          done
        · -- Case 2. h5 : ¬c ∈ X
          apply Exists.intro c
          rewrite [invRel_def, Tdef]
          show c ∈ X ∧ R c b ∨ c ∉ X ∧ S c b from
            Or.inr (And.intro h5 Scb)
          done
        done
      · -- Uniqueness
        fix a1 : U; fix a2 : U
        assume Ta1b : T a1 b
        assume Ta2b : T a2 b
        by_cases h5 : a1 ∈ X
        · -- Case 1. h5 : a1 ∈ X
          have h6 : a2 ∈ X := csb_cri_of_cri Ta1b Ta2b h5
          have Ra1b : R a1 b := csb_match_cri Ta1b h5
          have Ra2b : R a2 b := csb_match_cri Ta2b h6
          have h7 : b ∈ D := (R_match_AD.left Ra1b).right
          show a1 = a2 from
            fcnl_unique R_match_AD.right.right h7 Ra1b Ra2b
          done
        · -- Case 2. h5 : a1 ∉ X
          have h6 : a2 ∉ X := by
            by_contra h6
            show False from h5 (csb_cri_of_cri Ta2b Ta1b h6)
            done
          have Sa1b : S a1 b := csb_match_not_cri Ta1b h5
          have Sa2b : S a2 b := csb_match_not_cri Ta2b h6
          show a1 = a2 from
            fcnl_unique S_match_CB.right.right bB Sa1b Sa2b
          done
        done
      done
    done
  done