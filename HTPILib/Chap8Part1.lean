/- Copyright 2023-2025 Daniel J. Velleman -/

import HTPILib.Chap5
namespace HTPI

open Classical

/- Definitions -/
def equinum (U V : Type) : Prop :=
  ∃ (f : U → V), one_to_one f ∧ onto f

notation:50  U:50 " ∼ " V:50 => equinum U V

def Subtype_elt {U : Type} {A : Set U} {x : U} (h : x ∈ A) : ↑A :=
  Subtype.mk x h

def I (n : Nat) : Set Nat := {k : Nat | k < n}

def finite (U : Type) : Prop := ∃ (n : Nat), I n ∼ U

def denum (U : Type) : Prop := Nat ∼ U

def ctble (U : Type) : Prop := finite U ∨ denum U

def range {U V : Type} (f : U → V) : Set V := {y : V | ∃ (x : U), f x = y}

lemma elt_range {U V : Type} (f : U → V) (x : U) : f x ∈ range f := by
  define                 --Goal : ∃ (x_1 : U), f x_1 = f x
  apply Exists.intro x
  rfl
  done

def func_to_range {U V : Type} (f : U → V) (x : U) : range f :=
  Subtype_elt (elt_range f x)

def func_restrict {U V : Type}
  (f : U → V) (A : Set U) (x : A) : V := f x.val

def one_one_on {U V : Type} (f : U → V) (A : Set U) : Prop :=
  ∀ ⦃x1 x2 : U⦄, x1 ∈ A → x2 ∈ A → f x1 = f x2 → x1 = x2

def func_to_type {U V : Type} {B : Set V}
  (f : U → B) (x : U) : V := (f x).val

noncomputable def func_extend {U V : Type} {A : Set U}
  (f : A → V) (v : V) (u : U) : V :=
  if test : u ∈ A then f (Subtype_elt test) else v

def constant_func (U : Type) {V : Type} (v : V) (x : U) : V := v

def numElts {U : Type} (A : Set U) (n : Nat) : Prop := I n ∼ A

/- Section 8.1 -/
lemma id_one_one (U : Type) : one_to_one (@id U) := by
  fix x1 : U; fix x2 : U
  assume h : id x1 = id x2
  show x1 = x2 from h
  done

lemma id_onto (U : Type) : onto (@id U) := by
  fix y : U              --Goal : ∃ (x : U), id x = y
  apply Exists.intro y   --Goal : id y = y
  rfl
  done

theorem Theorem_8_1_3_1 (U : Type) : U ∼ U := by
  apply Exists.intro id
  show one_to_one id ∧ onto id from And.intro (id_one_one U) (id_onto U)
  done

theorem Theorem_8_1_3_2 {U V : Type}
    (h : U ∼ V) : V ∼ U := by
  obtain (f : U → V) (h1 : one_to_one f ∧ onto f) from h
  obtain (finv : V → U) (h2 : graph finv = inv (graph f)) from
    Theorem_5_3_1 f h1.left h1.right
  apply Exists.intro finv
  have h3 : finv ∘ f = id := Theorem_5_3_2_1 f finv h2
  have h4 : f ∘ finv = id := Theorem_5_3_2_2 f finv h2
  show one_to_one finv ∧ onto finv from
    And.intro (Theorem_5_3_3_1 finv f h4) (Theorem_5_3_3_2 finv f h3)
  done

theorem Theorem_8_1_3_3 {U V W : Type}
    (h1 : U ∼ V) (h2 : V ∼ W) : U ∼ W := by
  obtain (f : U → V) (h3 : one_to_one f ∧ onto f) from h1
  obtain (g : V → W) (h4 : one_to_one g ∧ onto g) from h2
  apply Exists.intro (g ∘ f)
  show one_to_one (g ∘ f) ∧ onto (g ∘ f) from
    And.intro (Theorem_5_2_5_1 f g h3.left h4.left)
    (Theorem_5_2_5_2 f g h3.right h4.right)
  done

theorem wishful_thinking?
    {U : Type} (A : Set U) : A ∼ A := Theorem_8_1_3_1 A

#check @wishful_thinking?   --∀ {U : Type} (A : Set U), ↑A ∼ ↑A

lemma I_def (k n : Nat) : k ∈ I n ↔ k < n := by rfl

lemma denum_def (U : Type) : denum U ↔ Nat ∼ U := by rfl

lemma ftr_def {U V : Type} (f : U → V) (x : U) :
    (func_to_range f x).val = f x := by rfl

lemma ftr_onto {U V : Type} (f : U → V) : onto (func_to_range f) := by
  fix y : range f              --y has type ↑(range f)
  have h1 : y.val ∈ range f := y.property
  define at h1                 --h1 : ∃ (x : U), f x = y.val
  obtain (x : U) (h2 : f x = y.val) from h1
  apply Exists.intro x         --Goal : func_to_range f x = y
  apply Subtype.ext            --Goal : (func_to_range f x).val = y.val
  rewrite [ftr_def, h2]
  rfl
  done

lemma ftr_one_one_of_one_one {U V : Type} {f : U → V}
    (h : one_to_one f) : one_to_one (func_to_range f) := by
  fix x1 : U; fix x2 : U
  assume h1 : func_to_range f x1 = func_to_range f x2
  have h2 : f x1 = f x2 :=
    calc f x1
      _ = (func_to_range f x1).val := (ftr_def f x1).symm
      _ = (func_to_range f x2).val := by rw [h1]
      _ = f x2 := ftr_def f x2
  show x1 = x2 from h x1 x2 h2
  done

theorem equinum_range {U V : Type} {f : U → V}
    (h : one_to_one f) : U ∼ range f := by
  apply Exists.intro (func_to_range f)
  show one_to_one (func_to_range f) ∧ onto (func_to_range f) from
    And.intro (ftr_one_one_of_one_one h) (ftr_onto f)
  done

lemma fr_def {U V : Type} (f : U → V) (A : Set U) (x : A) :
    func_restrict f A x = f x.val := by rfl

lemma fr_one_one_of_one_one_on {U V : Type} {f : U → V} {A : Set U}
    (h : one_one_on f A) : one_to_one (func_restrict f A) := by
  fix x1 : A; fix x2 : A                    --x1 and x2 have type ↑A
  assume h1 : func_restrict f A x1 = func_restrict f A x2
  rewrite [fr_def, fr_def] at h1            --h1 : f x1.val = f x2.val
  apply Subtype.ext                         --Goal : x1.val = x2.val
  show x1.val = x2.val from h x1.property x2.property h1
  done

lemma elt_image {U V : Type} {A : Set U} {x : U}
    (f : U → V) (h : x ∈ A) : f x ∈ image f A := by
  define                   --Goal : ∃ x_1 ∈ A, f x_1 = f x
  apply Exists.intro x     --Goal : x ∈ A ∧ f x = f x
  apply And.intro h
  rfl
  done

lemma fr_range {U V : Type} (f : U → V) (A : Set U) :
    range (func_restrict f A) = image f A := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ range (func_restrict f A) --Goal : y ∈ image f A
    define at h1
    obtain (a : A) (h2 : func_restrict f A a = y) from h1
    rewrite [←h2, fr_def]                     --Goal : f a.val ∈ image f A
    show f a.val ∈ image f A from elt_image f a.property
    done
  · -- (←)
    assume h1 : y ∈ image f A         --Goal : y ∈ range (func_restrict f A)
    define at h1
    obtain (a : U) (h2 : a ∈ A ∧ f a = y) from h1
    set aA : A := Subtype_elt h2.left
    have h3 : func_restrict f A aA = f a := fr_def f A aA
    rewrite [←h2.right, ←h3]
    show func_restrict f A aA ∈ range (func_restrict f A) from
      elt_range (func_restrict f A) aA
    done
  done

theorem equinum_image {U V : Type} {A : Set U} {f : U → V}
    (h : one_one_on f A) : A ∼ image f A := by
  rewrite [←fr_range f A]          --Goal : A ∼ range (func_restrict f A)
  have h1 : one_to_one (func_restrict f A) :=
    fr_one_one_of_one_one_on h
  show A ∼ range (func_restrict f A) from equinum_range h1
  done

lemma ftt_def {U V : Type} {B : Set V} (f : U → B) (x : U) :
    func_to_type f x = (f x).val := by rfl

lemma fe_elt {U V : Type} {A : Set U} (f : A → V) (v : V) (a : A) :
    func_extend f v a.val = f a := dif_pos a.property

example (U V : Type) (f : U → V) :
    func_to_type (func_to_range f) = f := by rfl

example (U V : Type) (A : Set U) (f : A → V) (v : V) :
    func_restrict (func_extend f v) A = f := sorry

lemma ftt_range_of_onto {U V : Type} {B : Set V} {f : U → B}
    (h : onto f) : range (func_to_type f) = B := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ range (func_to_type f)
    obtain (x : U) (h2 : func_to_type f x = y) from h1
    rewrite [←h2, ftt_def]
    show (f x).val ∈ B from (f x).property
    done
  · -- (←)
    assume h1 : y ∈ B
    set yB : B := Subtype_elt h1
    obtain (x : U) (h2 : f x = yB) from h yB
    apply Exists.intro x
    show func_to_type f x = y from
      calc func_to_type f x
        _ = (f x).val := ftt_def f x
        _ = yB.val := by rw [h2]
        _ = y := by rfl
    done
  done

lemma ftt_one_one_of_one_one {U V : Type} {B : Set V} {f : U → B}
    (h : one_to_one f) : one_to_one (func_to_type f) := by
  fix x1 : U; fix x2 : U
  assume h1 : func_to_type f x1 = func_to_type f x2
  have h2 : f x1 = f x2 := by
    apply Subtype.ext
    rewrite [ftt_def, ftt_def] at h1
    show (f x1).val = (f x2).val from h1
    done
  show x1 = x2 from h x1 x2 h2
  done

lemma fe_image {U V : Type} {A : Set U}
    (f : A → V) (v : V) : image (func_extend f v) A = range f := by
  apply Set.ext
  fix y : V
  apply Iff.intro
  · --
    assume h1 : y ∈ image (func_extend f v) A
    define at h1
    obtain (x : U) (h2 : x ∈ A ∧ func_extend f v x = y) from h1
    set xA : A := Subtype_elt h2.left
    have h3 : func_extend f v x = f xA := fe_elt f v xA
    rewrite [←h2.right, h3]
    show f xA ∈ range f from elt_range f xA
    done
  · --
    assume h1 : y ∈ range f
    define at h1
    obtain (xA : A) (h2 : f xA = y) from h1
    rewrite [←h2, ←fe_elt f v]
    show func_extend f v xA.val ∈ image (func_extend f v) A from
      elt_image (func_extend f v) xA.property
    done
  done

lemma fe_one_one_on_of_one_one {U V : Type} {A : Set U} {f : A → V}
    (h : one_to_one f) (v : V) : one_one_on (func_extend f v) A := by
  set F : U → V := func_extend f v
  define
  fix x1 : U; fix x2 : U
  assume h1 : x1 ∈ A
  assume h2 : x2 ∈ A
  assume h3 : F x1 = F x2
  set x1A : A := Subtype_elt h1
  set x2A : A := Subtype_elt h2
  have h4 : F x1 = f x1A := fe_elt f v x1A
  have h5 : F x2 = f x2A := fe_elt f v x2A
  rewrite [h4, h5] at h3       --h3 : f x1A = f x2A
  have h6 : x1A = x2A := h x1A x2A h3
  show x1 = x2 from
    calc x1
      _ = x1A.val := by rfl
      _ = x2A.val := by rw [h6]
      _ = x2 := by rfl
  done

theorem type_to_type_of_equinum {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) (v : V) :
    ∃ (f : U → V), one_one_on f A ∧ image f A = B := by
  obtain (g : A → B) (h1 : one_to_one g ∧ onto g) from h
  set gtt : A → V := func_to_type g
  set f : U → V := func_extend gtt v
  apply Exists.intro f
  apply And.intro
  · -- Proof of one_to_one_on f A
    have h2 : one_to_one gtt := ftt_one_one_of_one_one h1.left
    show one_one_on f A from fe_one_one_on_of_one_one h2 v
    done
  · -- Proof of image f A = B
    have h2 : range gtt = B := ftt_range_of_onto h1.right
    have h3 : image f A = range gtt := fe_image gtt v
    rewrite [h3, h2]
    rfl
    done
  done

/- Section 8.1½ -/
lemma numElts_def {U : Type} (A : Set U) (n : Nat) :
    numElts A n ↔ I n ∼ A := by rfl

lemma finite_def {U : Type} (A : Set U) :
    finite A ↔ ∃ (n : Nat), numElts A n := by rfl

lemma not_empty_iff_exists_elt {U : Type} {A : Set U} :
    ¬empty A ↔ ∃ (x : U), x ∈ A := by
  define : empty A
  double_neg
  rfl
  done

lemma elt_empty_implies {U : Type} {A : Set U} {x : U} {P : Prop}
    (h : empty A) : x ∈ A → P := by
  assume h1 : x ∈ A
  contradict h
  show ∃ (x : U), x ∈ A from Exists.intro x h1
  done

lemma one_one_on_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : one_one_on f A := by
  fix x1 : U; fix x2 : U
  show x1 ∈ A → x2 ∈ A → f x1 = f x2 → x1 = x2 from
    elt_empty_implies h
  done

lemma image_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : image f A = I 0 := sorry

theorem zero_elts_iff_empty {U : Type} (A : Set U) :
    numElts A 0 ↔ empty A := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 0
    define at h1
    obtain (f : I 0 → A) (h2 : one_to_one f ∧ onto f) from h1
    by_contra h3
    rewrite [not_empty_iff_exists_elt] at h3
    obtain (x : U) (h4 : x ∈ A) from h3
    set xA : A := Subtype_elt h4
    obtain (n : I 0) (h5 : f n = xA) from h2.right xA
    have h6 : n.val < 0 := n.property
    linarith
    done
  · -- (←)
    assume h1 : empty A
    rewrite [numElts_def]
    set f : U → Nat := constant_func U 0
    have h2 : one_one_on f A := one_one_on_empty f h1
    have h3 : image f A = I 0 := image_empty f h1
    have h4 : A ∼ image f A := equinum_image h2
    rewrite [h3] at h4
    show I 0 ∼ A from Theorem_8_1_3_2 h4
    done
  done

theorem nonempty_of_pos_numElts {U : Type} {A : Set U} {n : Nat}
    (h1 : numElts A n) (h2 : n > 0) : ∃ (x : U), x ∈ A := by
  define at h1
  obtain (f : I n → A) (h3 : one_to_one f ∧ onto f) from h1
  have h4 : 0 ∈ I n := h2
  set x : A := f (Subtype_elt h4)
  show ∃ (x : U), x ∈ A from Exists.intro x.val x.property
  done

def incr_from (k n : Nat) : Nat := if n < k then n else n + 1

lemma incr_from_lt {k n : Nat} (h : n < k) :
    incr_from k n = n := if_pos h

lemma incr_from_nlt {k n : Nat} (h : ¬n < k) :
    incr_from k n = n + 1 := if_neg h

lemma incr_from_iff (k n : Nat) : incr_from k n < k ↔ n < k := by
  apply Iff.intro
  · -- (→)
    assume h1 : incr_from k n < k
    by_contra h2
    rewrite [incr_from_nlt h2] at h1
    linarith  --h1 : n + 1 < k contradicts h2 : ¬n < k
    done
  · -- (←)
    assume h1 : n < k
    rewrite [incr_from_lt h1]
    show n < k from h1
    done
  done

lemma incr_from_one_one (k : Nat) :
    one_to_one (incr_from k) := by
  fix n1 : Nat; fix n2 : Nat
  assume h1 : incr_from k n1 = incr_from k n2
  have h2 : n1 < k ↔ n2 < k :=
    calc n1 < k
      _ ↔ incr_from k n1 < k := (incr_from_iff k n1).symm
      _ ↔ incr_from k n2 < k := by rw [h1]
      _ ↔ n2 < k := incr_from_iff k n2
  by_cases h3 : n1 < k
  · -- Case 1. h3 : n1 < k
    have h4 : n2 < k := h2.ltr h3
    rewrite [incr_from_lt h3, incr_from_lt h4] at h1
    show n1 = n2 from h1
    done
  · -- Case 2. h3 : ¬n1 < k
    have h4 : ¬n2 < k := by
      contradict h3 with h4
      show n1 < k from h2.rtl h4
      done
    rewrite [incr_from_nlt h3, incr_from_nlt h4] at h1
    linarith
    done
  done

lemma incr_from_image {k n : Nat} (h : k < n + 1) :
    image (incr_from k) (I n) = I (n + 1) \ {k} := by
  apply Set.ext
  fix m : Nat
  have h1 : m ∈ I (n + 1) \ {k} ↔ m < n + 1 ∧ m ≠ k := by rfl
  rewrite [h1]
  apply Iff.intro
  · -- (→)
    assume h2 : m ∈ image (incr_from k) (I n)
    obtain (t : Nat) (h3 : t ∈ I n ∧ incr_from k t = m) from h2
    rewrite [I_def] at h3
    by_cases h4 : t < k
    · -- Case 1. h4 : t < k
      rewrite [incr_from_lt h4] at h3
      have h5 : m < n + 1 := by linarith --m = t < n < n + 1
      have h6 : m ≠ k := by linarith     --m = t < k
      show m < n + 1 ∧ m ≠ k from And.intro h5 h6
      done
    · -- Case 2. h4 : ¬t < k
      rewrite [incr_from_nlt h4] at h3
      have h5 : m < n + 1 := by linarith --m = t + 1 and t < n
      have h6 : m ≠ k := by linarith     --m = t + 1 and ¬t < k
      show m < n + 1 ∧ m ≠ k from And.intro h5 h6
      done
    done
  · -- (→)
    assume h2 : m < n + 1 ∧ m ≠ k
    by_cases h3 : m < k
    · -- Case 1. h3 : m < k
      apply Exists.intro m
      rewrite [I_def]
      apply And.intro _ (incr_from_lt h3)
      linarith                        --m < k < n + 1
      done
    · -- Case 2. h3 : ¬m < k
      have h4 : m = k ∨ k < m := Nat.eq_or_lt_of_not_lt h3
      disj_syll h4 h2.right           --h4 : k < m
      have h5 : 1 ≤ m := by linarith
      obtain (t : Nat) (h6 : m = t + 1) from
        Nat.exists_eq_add_of_le' h5
      apply Exists.intro t
      rewrite [I_def, h6]
      have h7 : ¬t < k := by linarith --k < m = t + 1
      apply And.intro _ (incr_from_nlt h7)
      linarith                        --t + 1 = m < n + 1
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

lemma I_equinum_I_remove_one {k n : Nat}
    (h : k < n + 1) : I n ∼ ↑(I (n + 1) \ {k}) := by
  rewrite [←incr_from_image h]
  show I n ∼ image (incr_from k) (I n) from
    equinum_image (one_one_on_of_one_one (incr_from_one_one k) (I n))
  done

lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := sorry

theorem remove_one_numElts {U : Type} {A : Set U} {n : Nat} {a : U}
    (h1 : numElts A (n + 1)) (h2 : a ∈ A) : numElts (A \ {a}) n := by
  rewrite [numElts_def] at h1; rewrite [numElts_def]
    --h1 : I (n + 1) ∼ A;  Goal : I n ∼ ↑(A \ {a})
  obtain (f : Nat → U) (h3 : one_one_on f (I (n + 1)) ∧
    image f (I (n + 1)) = A) from type_to_type_of_equinum h1 a
  rewrite [←h3.right] at h2
  obtain (k : Nat) (h4 : k ∈ I (n + 1) ∧ f k = a) from h2
  have h5 : ↑(I (n + 1) \ {k}) ∼ ↑(A \ {a}) :=
    remove_one_equinum h3.left h3.right h4.left h4.right
  have h6 : k < n + 1 := h4.left
  have h7 : I n ∼ ↑(I (n + 1) \ {k}) := I_equinum_I_remove_one h6
  show I n ∼ ↑(A \ {a}) from Theorem_8_1_3_3 h7 h5
  done

lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := sorry

lemma one_one_on_I_1 {U : Type} (f : Nat → U) : one_one_on f (I 1) := by
  fix x1 : Nat; fix x2 : Nat
  assume h1 : x1 ∈ I 1
  assume h2 : x2 ∈ I 1
  assume h3 : f x1 = f x2
  define at h1; define at h2   --h1 : x1 < 1; h2 : x2 < 1
  linarith
  done

lemma image_I_1 {U : Type} (f : Nat → U) : image f (I 1) = {f 0} := by
  apply Set.ext
  fix y
  apply Iff.intro
  · -- (→)
    assume h1 : y ∈ image f (I 1)
    define at h1; define
    obtain (x : Nat) (h2 : x ∈ I 1 ∧ f x = y) from h1
    have h3 : x < 1 := h2.left
    have h4 : x = 0 := by linarith
    rewrite [←h2.right, h4]
    rfl
    done
  · -- (←)
    assume h1 : y ∈ {f 0}
    define at h1; define
    apply Exists.intro 0
    apply And.intro _ h1.symm
    define
    linarith
    done
  done

lemma singleton_one_elt {U : Type} (u : U) : numElts {u} 1 := by
  rewrite [numElts_def]  --Goal : I 1 ∼ {u}
  set f : Nat → U := constant_func Nat u
  have h1 : one_one_on f (I 1) := one_one_on_I_1 f
  have h2 : image f (I 1) = {f 0} := image_I_1 f
  have h3 : f 0 = u := by rfl
  rewrite [←h3, ←h2]
  show I 1 ∼ image f (I 1) from equinum_image h1
  done

theorem one_elt_iff_singleton {U : Type} (A : Set U) :
    numElts A 1 ↔ ∃ (x : U), A = {x} := by
  apply Iff.intro
  · -- (→)
    assume h1 : numElts A 1  --Goal : ∃ (x : U), A = {x}
    have h2 : 1 > 0 := by linarith
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
