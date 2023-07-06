import Chap8Part2
namespace HTPI.Exercises
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

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
lemma ctble_of_equinum_ctble {A B : Type} {X : Set A} {Y : Set B}
    (h1 : X ∼ Y) (h2 : ctble X) : ctble Y := sorry

-- 6.
theorem Exercise_8_1_1_b : denum { n : Int | even n } := sorry

-- Definition for next four exercises
def Rel_image {A B : Type} (R : Rel A B) (X : Set A) : Set B :=
  { y : B | ∃ (x : A), x ∈ X ∧ R x y }

-- 7.
lemma Rel_image_on_power_set {A B : Type} {R : Rel A B}
    {X U : Set A} {Y : Set B} (h1 : matching R X Y) (h2 : U ∈ 𝒫 X) :
    Rel_image R U ∈ 𝒫 Y := sorry

-- 8.
lemma Rel_image_inv {A B : Type} {R : Rel A B}
    {X U : Set A} {Y : Set B} (h1 : matching R X Y) (h2 : U ∈ 𝒫 X) :
    Rel_image (invRel R) (Rel_image R U) = U := sorry

-- 9.
lemma Rel_image_one_one_on {A B : Type} {R : Rel A B}
    {X : Set A} {Y : Set B} (h1 : matching R X Y) :
    one_one_on (Rel_image R) (𝒫 X) := sorry

-- 10.
lemma Rel_image_image {A B : Type} {R : Rel A B}
    {X : Set A} {Y : Set B} (h1 : matching R X Y) :
    image (Rel_image R) (𝒫 X) = 𝒫 Y := sorry

-- 11.
--Hint:  Use the previous two exercises.
theorem Exercise_8_1_5 {A B : Type} {X : Set A} {Y : Set B}
    (h1 : X ∼ Y) : 𝒫 X ∼ 𝒫 Y := sorry

-- 12.
theorem Exercise_8_1_17 {A : Type} {X Y : Set A}
    (h1 : X ⊆ Y) (h2 : ctble Y) : ctble X := sorry

-- 13.
theorem ctble_of_onto_func_from_N {A : Type} {X : Set A} {f : Nat → A}
    (h1 : ∀ x ∈ X, ∃ (n : Nat), f n = x) : ctble X := sorry

-- 14.
theorem ctble_of_one_one_func_to_N {A : Type} {X : Set A} {f : A → Nat}
    (h1 : one_one_on f X) : ctble X := sorry

/- Section 8.1½ -/
-- 1.
lemma remove_one_iff {A B : Type}
    {X : Set A} {Y : Set B} {R : Rel A B} (h1 : matching R X Y)
    {u : A} (h2 : u ∈ X) (v : B) {x : A} (h3 : x ∈ X \ {u}) :
    ∃ (w : A), w ∈ X ∧ ∀ (y : B), remove_one R u v x y ↔ R w y := sorry

-- 2.
lemma inv_one_match {A B : Type} (a : A) (b : B) :
    invRel (one_match a b) = one_match b a := sorry

-- 3.
theorem one_match_fcnl {A B : Type} (a : A) (b : B) :
    fcnl_on (one_match a b) {a} := sorry

-- 4.
--Hint:  Use the previous two exercises.
lemma one_match_match {A B : Type} (a : A) (b : B) :
    matching (one_match a b) {a} {b} := sorry

-- 5.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (Set_rp_below m) k (num_rp_below m k) := sorry

-- 6.
lemma prod_fcnl {A B C D : Type} {R : Rel A B} {S : Rel C D}
    {X : Set A} {Y : Set C} (h1 : fcnl_on R X) (h2 : fcnl_on S Y) :
    fcnl_on (R ×ᵣ S) (X ×ₛ Y) := sorry

-- 7.
--Hint:  Use the previous exercise.
lemma prod_match {A B C D : Type}
    {U : Set A} {V : Set B} {W : Set C} {X : Set D}
    {R : Rel A B} {S : Rel C D}
    (h1 : matching R U V) (h2 : matching S W X) :
    matching (R ×ᵣ S) (U ×ₛ W) (V ×ₛ X) := sorry

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

-- 9.
theorem Theorem_8_1_2_2
    {A B : Type} {U W : Set A} {V X : Set B}
    (h1 : empty (U ∩ W)) (h2 : empty (V ∩ X))
    (h3 : U ∼ V) (h4 : W ∼ X) : U ∪ W ∼ V ∪ X := sorry

-- 10.
lemma shift_I_equinum (n m : Nat) : I m ∼ I (n + m) \ I n := sorry

-- 11.
theorem Theorem_8_1_7 {A : Type} {X Y : Set A} {n m : Nat}
    (h1 : empty (X ∩ Y)) (h2 : numElts X n) (h3 : numElts Y m) :
    numElts (X ∪ Y) (n + m) := sorry

-- 12.
theorem equinum_sub {A B : Type} {X U : Set A} {Y : Set B}
    (h1 : X ∼ Y) (h2 : U ⊆ X) : ∃ (V : Set B), V ⊆ Y ∧ U ∼ V := sorry

-- 13.
theorem Exercise_8_1_8b {A : Type} {X U : Set A}
    (h1 : finite X) (h2 : U ⊆ X) : finite U := sorry

/- Section 8.2 -/
-- 1.
lemma pair_ctble {A : Type} (a b : A) : ctble {a, b} := sorry

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {A : Type} {X Y : Set A}
    (h1 : ctble X) (h2 : ctble Y) : ctble (X ∪ Y) := sorry

-- 3.
lemma seq_cons_image {A : Type} (X : Set A) (n : Nat) :
    image (seq_cons A) (X ×ₛ (seq_by_length X n)) =
      seq_by_length X (n + 1) := sorry

-- 4.
--Hint:  Use induction on the size of X
lemma set_to_list {A : Type} {X : Set A} (h : finite X) :
    ∃ (l : List A), ∀ (x : A), x ∈ l ↔ x ∈ X := sorry

-- 5.
--Hint:  Use the previous exercise and Theorem_8_2_4
theorem Like_Exercise_8_2_4 {A : Type} {X : Set A} (h : ctble X) :
    ctble { Y : Set A | Y ⊆ X ∧ finite Y } := sorry

-- 6.
theorem Exercise_8_2_6b (A B C : Type) :
    equinum (Univ (A × B → C)) (Univ (A → B → C)) := sorry

-- 7.
theorem Like_Exercise_8_2_7 : ∃ (P : Set (Set Nat)),
    partition P ∧ ctble P ∧ ∀ X ∈ P, ctble X := sorry

-- 8.
theorem unctbly_many_inf_set_nat :
    ¬ctble { X : Set Nat | ¬finite X } := sorry

-- 9.
theorem Exercise_8_2_8 {A : Type} {X Y : Set A}
    (h : empty (X ∩ Y)) : 𝒫 (X ∪ Y) ∼ 𝒫 X ×ₛ 𝒫 Y := sorry
