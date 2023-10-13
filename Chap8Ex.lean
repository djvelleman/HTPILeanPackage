import HTPILib.Chap8Part2
namespace HTPI.Exercises

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
lemma ctble_of_equinum_ctble {U V : Type} {A : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : ctble A) : ctble B := sorry

-- 6.
theorem Exercise_8_1_1_b : denum { n : Int | even n } := sorry

-- Definition for next four exercises
def Rel_image {U V : Type} (R : Rel U V) (A : Set U) : Set V :=
  { y : V | ∃ (x : U), x ∈ A ∧ R x y }

-- 7.
lemma Rel_image_on_power_set {U V : Type} {R : Rel U V}
    {A C : Set U} {B : Set V} (h1 : matching R A B) (h2 : C ∈ 𝒫 A) :
    Rel_image R C ∈ 𝒫 B := sorry

-- 8.
lemma Rel_image_inv {U V : Type} {R : Rel U V}
    {A C : Set U} {B : Set V} (h1 : matching R A B) (h2 : C ∈ 𝒫 A) :
    Rel_image (invRel R) (Rel_image R C) = C := sorry

-- 9.
lemma Rel_image_one_one_on {U V : Type} {R : Rel U V}
    {A : Set U} {B : Set V} (h1 : matching R A B) :
    one_one_on (Rel_image R) (𝒫 A) := sorry

-- 10.
lemma Rel_image_image {U V : Type} {R : Rel U V}
    {A : Set U} {B : Set V} (h1 : matching R A B) :
    image (Rel_image R) (𝒫 A) = 𝒫 B := sorry

-- 11.
--Hint:  Use the previous two exercises.
theorem Exercise_8_1_5 {U V : Type} {A : Set U} {B : Set V}
    (h1 : A ∼ B) : 𝒫 A ∼ 𝒫 B := sorry

-- 12.
theorem Exercise_8_1_17 {U : Type} {A B : Set U}
    (h1 : B ⊆ A) (h2 : ctble A) : ctble B := sorry

-- 13.
theorem ctble_of_onto_func_from_N {U : Type} {A : Set U} {f : Nat → U}
    (h1 : ∀ x ∈ A, ∃ (n : Nat), f n = x) : ctble A := sorry

-- 14.
theorem ctble_of_one_one_func_to_N {U : Type} {A : Set U} {f : U → Nat}
    (h1 : one_one_on f A) : ctble A := sorry

/- Section 8.1½ -/
-- 1.
lemma remove_one_iff {U V : Type}
    {A : Set U} {B : Set V} {R : Rel U V} (h1 : matching R A B)
    {u : U} (h2 : u ∈ A) (v : V) {x : U} (h3 : x ∈ A \ {u}) :
    ∃ (w : U), w ∈ A ∧ ∀ (y : V), remove_one R u v x y ↔ R w y := sorry

-- 2.
lemma inv_one_match {U V : Type} (a : U) (b : V) :
    invRel (one_match a b) = one_match b a := sorry

-- 3.
theorem one_match_fcnl {U V : Type} (a : U) (b : V) :
    fcnl_on (one_match a b) {a} := sorry

-- 4.
--Hint:  Use the previous two exercises.
lemma one_match_match {U V : Type} (a : U) (b : V) :
    matching (one_match a b) {a} {b} := sorry

-- 5.
lemma neb_nrpb (m : Nat) : ∀ ⦃k : Nat⦄, k ≤ m →
    num_elts_below (Set_rp_below m) k (num_rp_below m k) := sorry

-- 6.
lemma prod_fcnl {U V W X : Type} {R : Rel U V} {S : Rel W X}
    {A : Set U} {C : Set W} (h1 : fcnl_on R A) (h2 : fcnl_on S C) :
    fcnl_on (R ×ᵣ S) (A ×ₛ C) := sorry

-- 7.
--Hint:  Use the previous exercise.
lemma prod_match {U V W X : Type}
    {A : Set U} {B : Set V} {C : Set W} {D : Set X}
    {R : Rel U V} {S : Rel W X}
    (h1 : matching R A B) (h2 : matching S C D) :
    matching (R ×ᵣ S) (A ×ₛ C) (B ×ₛ D) := sorry

-- 8.
--Hint:  You might find it helpful to apply the theorem div_mod_char
--from the exercises of Section 6.4.
lemma qr_image (m n : Nat) :
    image (qr n) (I (m * n)) = I m ×ₛ I n := sorry

-- 9.
theorem Theorem_8_1_2_2
    {U V : Type} {A C : Set U} {B D : Set V}
    (h1 : empty (A ∩ C)) (h2 : empty (B ∩ D))
    (h3 : A ∼ B) (h4 : C ∼ D) : A ∪ C ∼ B ∪ D := sorry

-- 10.
lemma shift_I_equinum (n m : Nat) : I m ∼ I (n + m) \ I n := sorry

-- 11.
theorem Theorem_8_1_7 {U : Type} {A B : Set U} {n m : Nat}
    (h1 : empty (A ∩ B)) (h2 : numElts A n) (h3 : numElts B m) :
    numElts (A ∪ B) (n + m) := sorry

-- 12.
theorem equinum_sub {U V : Type} {A C : Set U} {B : Set V}
    (h1 : A ∼ B) (h2 : C ⊆ A) : ∃ (D : Set V), D ⊆ B ∧ C ∼ D := sorry

-- 13.
theorem Exercise_8_1_8b {U : Type} {A B : Set U}
    (h1 : finite A) (h2 : B ⊆ A) : finite B := sorry

-- 14.
--Hint:  Use Like_Exercise_6_2_16 from the exercises of Section 6.2
lemma N_not_finite : ¬finite (Univ Nat) := sorry

-- 15.
theorem denum_not_finite {U : Type} {A : Set U}
    (h : denum A) : ¬finite A := sorry

/- Section 8.2 -/
-- 1.
lemma pair_ctble {U : Type} (a b : U) : ctble {a, b} := sorry

-- 2.
--Hint:  Use the previous exercise and Theorem_8_2_2
theorem Theorem_8_2_1_2 {U : Type} {A B : Set U}
    (h1 : ctble A) (h2 : ctble B) : ctble (A ∪ B) := sorry

-- 3.
lemma seq_cons_image {U : Type} (A : Set U) (n : Nat) :
    image (seq_cons U) (A ×ₛ (seq_by_length A n)) =
      seq_by_length A (n + 1) := sorry

-- 4.
--Hint:  Use induction on the size of A
lemma set_to_list {U : Type} {A : Set U} (h : finite A) :
    ∃ (l : List U), ∀ (x : U), x ∈ l ↔ x ∈ A := sorry

-- 5.
--Hint:  Use the previous exercise and Theorem_8_2_4
theorem Like_Exercise_8_2_4 {U : Type} {A : Set U} (h : ctble A) :
    ctble { X : Set U | X ⊆ A ∧ finite X } := sorry

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
theorem Exercise_8_2_8 {U : Type} {A B : Set U}
    (h : empty (A ∩ B)) : 𝒫 (A ∪ B) ∼ 𝒫 A ×ₛ 𝒫 B := sorry

/- Section 8.3 -/
-- 1.
theorem CSB_func {U V : Type} {f : U → V} {g : V → U}
    (h1 : one_to_one f) (h2 : one_to_one g) : Univ U ∼ Univ V := sorry

-- 2.
theorem intervals_equinum :
    { x : Real | 0 < x ∧ x < 1 } ∼ { x : Real | 0 < x ∧ x ≤ 1 } := sorry

-- Definitions for next six exercises
def EqRel (A : Type) : Set (BinRel A) :=
  { R : BinRel A | equiv_rel R }

def Part (A : Type) : Set (Set (Set A)) :=
  { P : Set (Set A) | partition P }

def EqRelExt (A : Type) : Set (Set (A × A)) :=
  { E : Set (A × A) | ∃ (R : BinRel A), equiv_rel R ∧ extension R = E}

def shift_and_zero (X : Set Nat) : Set Nat :=
  { x + 2 | x ∈ X } ∪ {0}

def saz_pair (X : Set Nat) : Set (Set Nat) :=
  { shift_and_zero X, (Univ Nat) \ (shift_and_zero X) }

-- 3.
theorem EqRel_equinum_Part (A : Type) : EqRel A ∼ Part A := sorry

-- 4.
theorem EqRel_equinum_EqRelExt (A : Type) :
    EqRel A ∼ EqRelExt A := sorry

-- 5.
theorem EqRel_Nat_equinum_sub_PN :
    ∃ (D : Set (Set Nat)), D ⊆ 𝒫 (Univ Nat) ∧ EqRel Nat ∼ D := sorry

-- 6.
theorem saz_pair_part (X : Set Nat) : partition (saz_pair X) := sorry

-- 7.
theorem sub_EqRel_Nat_equinum_PN :
    ∃ (C : Set (BinRel Nat)), C ⊆ EqRel Nat ∧ C ∼ 𝒫 (Univ Nat) := sorry

-- 8.
theorem EqRel_Nat_equinum_PN : EqRel Nat ∼ 𝒫 (Univ Nat) := sorry