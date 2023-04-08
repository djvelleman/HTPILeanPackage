import Chap7
namespace HTPI
set_option pp.funBinderTypes true

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod_ex {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := sorry

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := sorry

-- 3.
theorem Exercise_7_1_5 (a b d : Nat) (n : Int) (h1 : gcd a b = d) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑d : Int) ∣ n := sorry

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := sorry

-- 5.
theorem gcd_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
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
lemma fd_le_prime_fac_ex (n : Nat) : ∀ (k : Nat),
    k ∣ (n + 2) → le_list (first_div (n + 2)) (prime_fac k) := sorry

-- 3.
theorem list_elt_dvd_prod (n : Nat) :
    ∀ (l : List Nat), n ∈ l → n ∣ (prod l) := sorry
-- Hint:  Start with apply List.rec

-- 4.
theorem Exercise_7_2_5 {a b : Nat} (h1 : a ≥ 1) (h2 : b ≥ 1) :
    rel_prime a b ↔ (¬∃ (p : Nat), prime p ∧
      p ∈ prime_fac a ∧ p ∈ prime_fac b) := sorry

-- 5.
theorem Exercise_7_2_6_ex (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 6.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 7.
theorem Exercise_7_2_9
    {a b d j k : Nat} (h1 : d ≠ 0) (h2 : d = gcd a b)
    (h3 : a = j * d) (h4 : b = k * d) : rel_prime j k := sorry

-- 8.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry