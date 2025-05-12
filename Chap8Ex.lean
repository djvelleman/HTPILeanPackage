import HTPILib.Chap8Part2
namespace HTPI.Exercises

open Classical

/- Section 8.1 -/
-- 1.
--Hint:  Use Exercise_6_1_16a2 from the exercises of Section 6.1
lemma fnz_odd (k : Nat) : fnz (2 * k + 1) = -↑(k + 1) := sorry

-- 2.
lemma fnz_fzn : fnz ∘ fzn = id  := sorry

-- 3.
lemma tri_step (k : Nat) : tri (k + 1) = tri k + k + 1 := sorry

-- 4.
lemma tri_incr {j k : Nat} (h1 : j ≤ k) : tri j ≤ tri k := sorry

-- 5.
example {U V : Type} (f : U → V) : range f = Ran (graph f) := sorry

-- 6.
lemma onto_iff_range_eq_univ {U V : Type} (f : U → V) :
    onto f ↔ range f = Univ V := sorry

-- 7.
-- Don't use ctble_iff_set_nat_equinum to prove this lemma
lemma ctble_of_ctble_equinum {U V : Type}
    (h1 : U ∼ V) (h2 : ctble U) : ctble V := sorry

-- 8.
theorem Exercise_8_1_1_b : denum {n : Int | even n} := sorry

-- 9.
theorem equinum_iff_inverse_pair (U V : Type) :
    U ∼ V ↔ ∃ (f : U → V) (g : V → U), f ∘ g = id ∧ g ∘ f = id := sorry

-- 10.
lemma image_comp_id {U V : Type} {f : U → V} {g : V → U}
    (h : g ∘ f = id) : (image g) ∘ (image f) = id := sorry

-- 11.
theorem Exercise_8_1_5_1 {U V : Type}
    (h : U ∼ V) : Set U ∼ Set V := sorry

-- Definition for next three exercises
def val_image {U : Type} (A : Set U) (X : Set A) : Set U :=
  {y : U | ∃ x ∈ X, x.val = y}

-- 12.
lemma subset_of_val_image_eq {U : Type} {A : Set U} {X1 X2 : Set A}
    (h : val_image A X1 = val_image A X2) : X1 ⊆ X2 := sorry

-- 13.
lemma val_image_one_one {U : Type} (A : Set U) :
    one_to_one (val_image A) := sorry

-- 14.
lemma range_val_image {U : Type} (A : Set U) :
    range (val_image A) = 𝒫 A := sorry

-- 15.
lemma Set_equinum_powerset {U : Type} (A : Set U) :
    Set A ∼ 𝒫 A := sorry

-- 16.
--Hint:  Use Exercise_8_1_5_1 and Set_equinum_powerset.
theorem Exercise_8_1_5_2 {U V : Type} {A : Set U} {B : Set V}
    (h : A ∼ B) : 𝒫 A ∼ 𝒫 B := sorry

-- 17.
example (U V : Type) (A : Set U) (f : A → V) (v : V) :
    func_restrict (func_extend f v) A = f := sorry

-- 18.
theorem Theorem_8_1_5_3_type {U : Type} :
    ctble U ↔ ∃ (f : U → Nat), one_to_one f := sorry

-- 19.
theorem ctble_set_of_ctble_type {U : Type}
    (h : ctble U) (A : Set U) : ctble A := sorry

-- 20.
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

/- Section 8.1½ -/
-- 1.
lemma image_empty {U : Type} {A : Set U}
    (f : U → Nat) (h : empty A) : image f A = I 0 := sorry

-- 2.
lemma remove_one_equinum
    {U V : Type} {A : Set U} {B : Set V} {a : U} {b : V} {f : U → V}
    (h1 : one_one_on f A) (h2 : image f A = B)
    (h3 : a ∈ A) (h4 : f a = b) : ↑(A \ {a}) ∼ ↑(B \ {b}) := sorry

-- 3.
lemma singleton_of_diff_empty {U : Type} {A : Set U} {a : U}
    (h1 : a ∈ A) (h2 : empty (A \ {a})) : A = {a} := sorry

-- 4.
lemma eq_zero_of_I_zero_equinum {n : Nat} (h : I 0 ∼ I n) : n = 0 := sorry

-- 5.
--Hint: use mathematical induction
theorem Exercise_8_1_6a : ∀ ⦃m n : Nat⦄, (I m ∼ I n) → m = n := sorry

-- 6.
theorem Exercise_8_1_6b {U : Type} {A : Set U} {m n : Nat}
    (h1 : numElts A m) (h2 : numElts A n) : m = n := sorry

-- 7.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (set_rp_below m) k = num_rp_below m k := sorry

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

-- Definitions for next two exercises
lemma is_elt_snd_of_not_fst {U : Type} {A C : Set U} {x : U}
    (h1 : x ∈ A ∪ C) (h2 : x ∉ A) : x ∈ C := by
  disj_syll h1 h2
  show x ∈ C from h1
  done

def elt_snd_of_not_fst {U : Type} {A C : Set U} {x : ↑(A ∪ C)}
  (h : x.val ∉ A) : C :=
  Subtype_elt (is_elt_snd_of_not_fst x.property h)

noncomputable def func_union {U V : Type} {A C : Set U}
  (f : A → V) (g : C → V) (x : ↑(A ∪ C)) : V :=
  if test : x.val ∈ A then f (Subtype_elt test)
    else g (elt_snd_of_not_fst test)

-- 9.
lemma func_union_one_one {U V : Type} {A C : Set U}
    {f : A → V} {g : C → V} (h1 : empty (range f ∩ range g))
    (h2 : one_to_one f) (h3 : one_to_one g) :
    one_to_one (func_union f g) := sorry

-- 10.
lemma func_union_range {U V : Type} {A C : Set U}
    (f : A → V) (g : C → V) (h : empty (A ∩ C)) :
    range (func_union f g) = range f ∪ range g := sorry

-- 11.
--Hint:  Use the last two exercises.
theorem Theorem_8_1_2_2
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : empty (A ∩ C)) (h2 : empty (B ∩ D))
    (h3 : A ∼ B) (h4 : C ∼ D) : ↑(A ∪ C) ∼ ↑(B ∪ D) := sorry

-- 12.
lemma shift_I_equinum (n m : Nat) : I m ∼ ↑(I (n + m) \ I n) := sorry

-- 13.
theorem Theorem_8_1_7 {U : Type} {A B : Set U} {n m : Nat}
    (h1 : empty (A ∩ B)) (h2 : numElts A n) (h3 : numElts B m) :
    numElts (A ∪ B) (n + m) := sorry

-- 14.
theorem equinum_sub {U V : Type} {A C : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : C ⊆ A) : ∃ (D : Set V), D ⊆ B ∧ C ∼ D := sorry

-- 15.
theorem Exercise_8_1_8b {U : Type} {A B : Set U}
    (h1 : finite A) (h2 : B ⊆ A) : finite B := sorry

-- 16.
theorem finite_bdd {A : Set Nat} (h : finite A) :
    ∃ (m : Nat), ∀ n ∈ A, n < m := sorry

-- 17.
lemma N_not_finite : ¬finite Nat := sorry

-- 18.
theorem denum_not_finite (U : Type)
    (h : denum U) : ¬finite U := sorry

-- 19.
--Hint:  Use Like_Exercise_6_2_16 from the exercises of Section 6.2.
theorem Exercise_6_2_16 {U : Type} {f : U → U}
    (h1 : one_to_one f) (h2 : finite U) : onto f := sorry

/- Section 8.2 -/
-- 1.
lemma pair_ctble {U : Type}
    (a b : U) : ctble ↑({a, b} : Set U) := sorry

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {U : Type} {A B : Set U}
    (h1 : ctble A) (h2 : ctble B) : ctble ↑(A ∪ B) := sorry

-- 3.
lemma remove_empty_union_eq {U : Type} (F : Set (Set U)) :
    ⋃₀ {A : Set U | A ∈ F ∧ ¬empty A} = ⋃₀ F := sorry

-- 4.
lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

-- 5.
--Hint:  Apply Theorem_8_2_4 to the set Univ U
theorem Theorem_8_2_4_type {U : Type}
    (h : ctble U) : ctble (List U) := sorry

-- 6.
def list_to_set (U : Type) (l : List U) : Set U := {x : U | x ∈ l}

lemma list_to_set_def (U : Type) (l : List U) (x : U) :
    x ∈ list_to_set U l ↔ x ∈ l := by rfl

--Hint:  Use induction on the size of A
lemma set_from_list {U : Type} {A : Set U} (h : finite A) :
    ∃ (l : List U), list_to_set U l = A := sorry

-- 7.
--Hint:  Use the previous exercise and Theorem_8_2_4_type
theorem Like_Exercise_8_2_4 (U : Type) (h : ctble U) :
    ctble {X : Set U | finite X} := sorry

-- 8.
theorem Exercise_8_2_6b (U V W : Type) :
     ((U × V) → W) ∼ (U → V → W) := sorry

-- 9.
theorem Like_Exercise_8_2_7 : ∃ (P : Set (Set Nat)),
    partition P ∧ denum P ∧ ∀ X ∈ P, denum X := sorry

-- 10.
theorem unctbly_many_inf_set_nat :
    ¬ctble {X : Set Nat | ¬finite X} := sorry

-- 11.
theorem Exercise_8_2_8 {U : Type} {A B : Set U}
    (h : empty (A ∩ B)) : 𝒫 (A ∪ B) ∼ 𝒫 A ×ₛ 𝒫 B := sorry

/- Section 8.3 -/
-- 1.
lemma csb_func_graph_not_X {U V : Type} {X : Set U} {x : U}
    (f : U → V) (g : V → U) (h : x ∉ X) (y : V) :
    (x, y) ∈ csb_func_graph f g X ↔ g y = x := sorry

-- 2.
theorem intervals_equinum :
    {x : Real | 0 < x ∧ x < 1} ∼ {x : Real | 0 < x ∧ x ≤ 1} := sorry

-- 3.
--Hint for proof:  First show that `extension R = extension S`, and then use the fact
--that `R` and `S` can be determined from `extension R` and `extension S` (see Section 4.3).
theorem relext {U V : Type} {R S : Rel U V}
    (h : ∀ (u : U) (v : V), R u v ↔ S u v) : R = S := sorry

-- Definitions for next six exercises
def EqRel (U : Type) : Set (BinRel U) :=
  {R : BinRel U | equiv_rel R}

def Part (U : Type) : Set (Set (Set U)) :=
  {P : Set (Set U) | partition P}

def EqRelExt (U : Type) : Set (Set (U × U)) :=
  {E : Set (U × U) | ∃ (R : BinRel U), equiv_rel R ∧ extension R = E}

def shift_and_zero (X : Set Nat) : Set Nat :=
  {x + 2 | x ∈ X} ∪ {0}

def shift_and_zero_comp (X : Set Nat) : Set Nat :=
  {n : Nat | n ∉ shift_and_zero X}

def saz_pair (X : Set Nat) : Set (Set Nat) :=
  {shift_and_zero X, shift_and_zero_comp X}

-- 4.
theorem EqRel_equinum_Part (U : Type) : EqRel U ∼ Part U := sorry

-- 5.
theorem EqRel_equinum_EqRelExt (U : Type) :
    EqRel U ∼ EqRelExt U := sorry

-- 6.
theorem EqRel_Nat_to_Set_Nat :
    ∃ (f : EqRel Nat → Set Nat), one_to_one f := sorry

-- 7.
theorem saz_pair_part (X : Set Nat) : saz_pair X ∈ Part Nat := sorry

-- 8.
theorem Set_Nat_to_EqRel_Nat :
    ∃ (f : Set Nat → EqRel Nat), one_to_one f := sorry

-- 9.
theorem EqRel_Nat_equinum_Set_Nat : EqRel Nat ∼ Set Nat := sorry
