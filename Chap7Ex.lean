import HTPILib.Chap7
namespace HTPI.Exercises

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := sorry

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := sorry

-- 3.
theorem Exercise_7_1_5 (a b : Nat) (n : Int) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑(gcd a b) : Int) ∣ n := sorry

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
lemma Lemma_7_1_10a {a b : Nat}
    (n : Nat) (h : a ∣ b) : (n * a) ∣ (n * b) := sorry

lemma Lemma_7_1_10b {a b n : Nat}
    (h1 : n ≠ 0) (h2 : (n * a) ∣ (n * b)) : a ∣ b := sorry

lemma Lemma_7_1_10c {a b : Nat}
    (h1 : a ∣ b) (h2 : b ∣ a) : a = b := sorry

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := sorry

/- Section 7.2 -/
-- 1.
lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ (a : Nat), a ∈ l → a ≠ 0) → prod l ≠ 0 := sorry

-- 3.
theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := sorry

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := sorry

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := sorry

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := sorry

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry

/- Section 7.3 -/
-- 1.
theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := sorry

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := sorry

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := sorry

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := sorry

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := sorry

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := sorry

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := sorry

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := sorry

-- 10.
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := sorry

--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute [a]_m ^ 0 * [1]_m in two ways:
--by Theorem_7_3_6_7, [a] ^ 0 * [1]_m = [a]_m ^ 0
--by ring, [a]_m ^ 0 * [1]_m = [1]_m.
lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

-- 2.
lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

-- 3.
lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

-- 4.
lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    a ^ (phi m + 1) ≡ a (MOD m) := sorry

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    [a]_m * [a ^ p]_m = [1]_m := sorry

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    a ^ p ≡ a ^ q (MOD m) := sorry

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ (k : Nat), k < p → num_rp_below p (k + 1) = k := sorry

-- 2.
lemma three_prime : prime 3 := sorry

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    ↑(a ^ 560) ≡ 1 (MOD 3) := sorry

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := sorry

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : b ^ 2 ≡ 1 (MOD n)) :
    b ≡ 1 (MOD n) ∨ b ≡ -1 (MOD n) := sorry