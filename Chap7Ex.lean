import Chap7
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod_ex {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

-- 2.
lemma gcd_comm_lt_ex {a b : Nat} (h : a < b) : gcd a b = gcd b a := sorry

theorem gcd_comm_ex (a b : Nat) : gcd a b = gcd b a := sorry

-- 3.
theorem Exercise_7_1_5 (a b d : Nat) (n : Int) (h1 : gcd a b = d) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑d : Int) ∣ n := sorry

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := sorry

-- 5.
theorem gcd_is_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
    gcd a b ≠ 0 := sorry

-- 6.
theorem gcd_greatest {a b d : Nat} (h1 : gcd a b ≠ 0)
    (h2 : d ∣ a) (h3 : d ∣ b) : d ≤ gcd a b := sorry

-- 7.
lemma Lemma_7_1_10a {a b : Nat} (n : Nat) (h : a ∣ b) :
    (n * a) ∣ (n * b) := sorry

lemma Lemma_7_1_10b {a b : Nat} (h1 : a ∣ b) (h2 : b ∣ a) :
    a = b := sorry

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := sorry

/- Section 7.2 -/
-- 1.
lemma dvd_prime_ex {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

-- 2.
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ (a : Nat), a ∈ l → a ≠ 0) → prod l ≠ 0 := sorry
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful

-- 3.
theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := sorry

-- 4.
theorem rel_prime_symm_ex {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

-- 5.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := sorry

-- 6.
theorem Exercise_7_2_6_ex (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 7.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 8.
theorem Exercise_7_2_9
    {a b d j k : Nat} (h1 : d ≠ 0) (h2 : d = gcd a b)
    (h3 : a = j * d) (h4 : b = k * d) : rel_prime j k := sorry

-- 9.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry

/- Section 7.3 -/
-- 1.
theorem congr_trans_ex {m : Nat} : ∀ {a b c : Int},
    congr_mod m a b → congr_mod m b c → congr_mod m a c := sorry

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + cc m 0 = X := sorry

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = cc m 0 := sorry

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := sorry

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = cc m 0) (h2 : X + Y2 = cc m 0) : Y1 = Y2 := sorry

-- 6.
theorem Theorem_7_3_10 (m a d : Nat) (b : Int) (h1 : d = gcd m a) :
    ¬(↑d : Int) ∣ b → ¬∃ (x : Int), congr_mod m (a * x) b := sorry

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    congr_mod (n * m) (n * a) (n * b) ↔  congr_mod m a b := sorry

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : congr_mod m a b) :
    ∀ (n : Nat), congr_mod m (a ^ n) (b ^ n) := sorry

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute (cc m a) ^ 0 * (cc m 1) in two ways:
--by Theorem_7_3_6_7, (cc m a) ^ 0 * (cc m 1) = (cc m a) ^ 0
--by ring, (cc m a) ^ 0 * (cc m 1) = cc m 1.
lemma Exercise_7_4_5_Int_ex (m : Nat) (a : Int) :
    ∀ (n : Nat), (cc m a) ^ n = cc m (a ^ n) := sorry

-- 2.
lemma left_inv_one_one_below_ex {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

-- 3.
lemma comp_perm_below_ex {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

-- 4.
lemma perm_below_fixed_ex {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    congr_mod m (a ^ (phi m + 1)) a := sorry

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    (cc m a) * (cc m ↑(a ^ p)) = cc m 1 := sorry

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    congr_mod m (a ^ p) (a ^ q) := sorry

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime_ex {p : Nat} (h1 : prime p) :
    ∀ (k : Nat), k < p → num_rp_below p (k + 1) = k := sorry

-- 2.
lemma three_prime : prime 3 := sorry

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    congr_mod 3 ↑(a ^ 560) 1 := sorry

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := sorry

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : congr_mod n (b ^ 2) 1) :
    congr_mod n b 1 ∨ congr_mod n b (-1) := sorry