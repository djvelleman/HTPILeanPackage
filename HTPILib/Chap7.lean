import Chap6
namespace HTPI
set_option pp.funBinderTypes true

/- Section 7.1 -/
theorem dvd_mod_of_dvd_a_b {a b d : Nat}
    (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a % b) := by
  let q : Nat := a / b
  have h3 : b * q + a % b = a := Nat.div_add_mod a b
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  define    --Goal : ∃ (c : Nat), a % b = d * c
  apply Exists.intro (j - k * q)
  show a % b = d * (j - k * q) from
    calc a % b
      _ = b * q + a % b - b * q := (Nat.add_sub_cancel_left _ _).symm
      _ = a - b * q := by rw [h3]
      _ = d * j - d * (k * q) := by rw [h4, h5, mul_assoc]
      _ = d * (j - k * q) := (Nat.mul_sub_left_distrib _ _ _).symm
  done

theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := by
  let q : Nat := a / b
  have h3 : b * q + a % b = a := Nat.div_add_mod a b
  obtain (j : Nat) (h4 : b = d * j) from h1
  obtain (k : Nat) (h5 : a % b = d * k) from h2
  rewrite [h5, h4] at h3  --h3 : d * j * q + d * k = a
  define                  --Goal : ∃ (c : Nat), a = d * c
  apply Exists.intro (j * q + k)
  rewrite [←h3]           --Goal : d * j * q + d * k = d * (j * q + k)
  ring
  done

lemma mod_succ_lt (a n : Nat) : a % (n + 1) < n + 1 := by
  have h : n + 1 > 0 := Nat.succ_pos n
  show a % (n + 1) < n + 1 from Nat.mod_lt a h
  done

def gcd (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 =>
      have : a % (n + 1) < n + 1 := mod_succ_lt a n
      gcd (n + 1) (a % (n + 1))
  termination_by gcd a b => b

#eval gcd 672 161    --Answer: 7

lemma gcd_base (a : Nat) : gcd a 0 = a := by rfl

lemma plus_one_of_ne {n : Nat} (h : n ≠ 0) :
    ∃ (k : Nat), n = k + 1 := by
  have h2 : n ≥ 1 := Nat.pos_of_ne_zero h
  apply Exists.intro (n - 1)
  show n = n - 1 + 1 from (Nat.sub_add_cancel h2).symm
  done

lemma gcd_of_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd a b = gcd b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from plus_one_of_ne h
  rewrite [h2]   --Goal : gcd a (n + 1) = gcd (n + 1) (a % (n + 1))
  rfl
  done

lemma mod_nonzero_lt (a : Nat) {b : Nat} (h : b ≠ 0) : a % b < b := by
  have h1 : b > 0 := Nat.pos_of_ne_zero h
  show a % b < b from Nat.mod_lt a h1
  done

lemma dvd_self (n : Nat) : n ∣ n := by
  apply Exists.intro 1
  ring
  done

theorem gcd_dvd : ∀ (b a : Nat), (gcd a b) ∣ a ∧ (gcd a b) ∣ b := by
  by_strong_induc
  fix b : Nat
  assume ih : ∀ (b_1 : Nat), b_1 < b →
    ∀ (a : Nat), (gcd a b_1) ∣ a ∧ (gcd a b_1) ∣ b_1
  fix a : Nat
  by_cases h1 : b = 0
  · -- Case 1. h1 : b = 0
    rewrite [h1, gcd_base]   --Goal: a ∣ a ∧ a ∣ 0
    apply And.intro (dvd_self a)
    define
    apply Exists.intro 0
    rfl
    done
  · -- Case 2. h1 : b ≠ 0
    rewrite [gcd_of_nonzero a h1]
      --Goal : gcd b (a % b) ∣ a ∧ gcd b (a % b) ∣ b
    have h2 : a % b < b := mod_nonzero_lt a h1
    have h3 : (gcd b (a % b)) ∣ b ∧ (gcd b (a % b)) ∣ (a % b) :=
      ih (a % b) h2 b
    apply And.intro _ h3.left
    show (gcd b (a % b)) ∣ a from dvd_a_of_dvd_b_mod h3.left h3.right
  done

theorem gcd_dvd_left (a b : Nat) : (gcd a b) ∣ a := (gcd_dvd b a).left

theorem gcd_dvd_right (a b : Nat) : (gcd a b) ∣ b := (gcd_dvd b a).right

mutual
  def gcd_c1 (a b : Nat) : Int :=
    match b with
      | 0 => 1
      | n + 1 => 
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c2 (n + 1) (a % (n + 1))
          --Corresponds to s = t'

  def gcd_c2 (a b : Nat) : Int :=
    match b with
      | 0 => 0
      | n + 1 =>
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c1 (n + 1) (a % (n + 1)) -
          (gcd_c2 (n + 1) (a % (n + 1))) * ↑(a / (n + 1))
          --Corresponds to t = s' - t'q
end
  termination_by
    gcd_c1 a b => b
    gcd_c2 a b => b

lemma gcd_c1_base (a : Nat) : gcd_c1 a 0 = 1 := by rfl

lemma gcd_c1_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c1 a b = gcd_c2 b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from plus_one_of_ne h
  rewrite [h2]
  rfl
  done

lemma gcd_c2_base (a : Nat) : gcd_c2 a 0 = 0 := by rfl

lemma gcd_c2_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c2 a b = gcd_c1 b (a % b) - (gcd_c2 b (a % b)) * ↑(a / b) := by
  obtain (n : Nat) (h2 : b = n + 1) from plus_one_of_ne h
  rewrite [h2]
  rfl
  done

theorem gcd_lin_comb : ∀ (b a : Nat),
    (gcd_c1 a b) * ↑a + (gcd_c2 a b) * ↑b = ↑(gcd a b) := by
  by_strong_induc
  fix b : Nat
  assume ih : ∀ (b_1 : Nat), b_1 < b → ∀ (a : Nat),
    (gcd_c1 a b_1) * ↑a + (gcd_c2 a b_1) * ↑b_1 = ↑(gcd a b_1)
  fix a : Nat
  by_cases h1 : b = 0
  · -- Case 1. h1 : b = 0
    rewrite [h1, gcd_c1_base, gcd_c2_base, gcd_base]
      --Goal : 1 * ↑a + 0 * ↑0 = ↑a
    norm_num
    done
  · -- Case 2. h1 : b ≠ 0
    rewrite [gcd_c1_nonzero a h1, gcd_c2_nonzero a h1, gcd_of_nonzero a h1]
    let r : Nat := a % b
    let q : Nat := a / b
    let s : Int := gcd_c1 b r
    let t : Int := gcd_c2 b r
    have hr : a % b = r := by rfl
    have hq : a / b = q := by rfl
    have hs : gcd_c1 b r = s := by rfl
    have ht : gcd_c2 b r = t := by rfl
    rewrite [hr, hq, hs, ht]
      --Goal : t * ↑a + (s - t * ↑q) * ↑b = ↑(gcd b r)
    have h2 : r < b := mod_nonzero_lt a h1
    have h3 : s * ↑b + t * ↑r = ↑(gcd b r) := ih r h2 b
    have h4 : b * q + r = a := Nat.div_add_mod a b
    rewrite [←h3, ←h4]
    rewrite [Nat.cast_add, Nat.cast_mul]
      --Goal : t * (↑b * ↑q + ↑r) + (s - t * ↑q) * ↑b = s * ↑b + t * ↑r
    ring
    done
  done

#eval gcd_c1 672 161  --Answer: 6
#eval gcd_c2 672 161  --Answer: -25
  --Note 6 * 672 - 25 * 161 = 4032 - 4025 = 7 = gcd 672 161

theorem Theorem_7_1_6 {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) :
    d ∣ gcd a b := by
  rewrite [←Int.coe_nat_dvd]    --Goal : ↑d ∣ ↑(gcd a b)
  let s : Int := gcd_c1 a b
  let t : Int := gcd_c2 a b
  have h3 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
  rewrite [←h3]                 --Goal : ↑d ∣ s * ↑a + t * ↑b
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  rewrite [h4, h5, Nat.cast_mul, Nat.cast_mul]
    --Goal : ↑d ∣ s * (↑d * ↑j) + t * (↑d * ↑k)
  define
  apply Exists.intro (s * ↑j + t * ↑k)
  ring
  done

/- Section 7.2 -/ 
def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n

def rel_prime (a b : Nat) : Prop := gcd a b = 1

theorem Theorem_7_2_2 {a b c : Nat}
    (h1 : c ∣ a * b) (h2 : rel_prime a c) : c ∣ b := by
  rewrite [←Int.coe_nat_dvd]  --Goal : ↑c ∣ ↑b
  define at h1; define at h2; define
  obtain (j : Nat) (h3 : a * b = c * j) from h1
  let s : Int := gcd_c1 a c
  let t : Int := gcd_c2 a c
  have h4 : s * ↑a + t * ↑c = ↑(gcd a c) := gcd_lin_comb c a
  rewrite [h2, Nat.cast_one] at h4  --h4 : s * ↑a + t * ↑c = (1 : Int)
  apply Exists.intro (s * ↑j + t * ↑b)
  show ↑b = ↑c * (s * ↑j + t * ↑b) from
    calc ↑b
      _ = (1 : Int) * ↑b := (one_mul _).symm
      _ = (s * ↑a + t * ↑c) * ↑b := by rw [h4]
      _ = s * (↑a * ↑b) + t * ↑c * ↑b := by ring
      _ = s * (↑c * ↑j) + t * ↑c * ↑b := by
          rw [←Nat.cast_mul a b, h3, Nat.cast_mul c j]
      _ = ↑c * (s * ↑j + t * ↑b) := by ring
  done

lemma le_nonzero_prod_left {a b : Nat} (h : a * b ≠ 0) : a ≤ a * b := by
  have h1 : b ≠ 0 := by
    contradict h with h1
    rewrite [h1]
    norm_num
    done
  have h2 : 1 ≤ b := Nat.pos_of_ne_zero h1
  show a ≤ a * b from
    calc a
        = a * 1 := (mul_one a).symm
      _ ≤ a * b := Nat.mul_le_mul_left a h2
  done

lemma le_nonzero_prod_right {a b : Nat} (h : a * b ≠ 0) : b ≤ a * b := by
  rewrite [mul_comm]
  rewrite [mul_comm] at h
  show b ≤ b * a from le_nonzero_prod_left h
  done

lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := by
  obtain (b : Nat) (h3 : p = a * b) from h2
  define at h1
  contradict h1.right with h4
    --Goal : ∃ (a b : Nat), a * b = p ∧ a < p ∧ b < p
  demorgan at h4
  apply Exists.intro a
  apply Exists.intro b
  apply And.intro h3.symm   --Goal : a < p ∧ b < p
  have h5 : a * b ≠ 0 := by linarith
  have h6 : a ≤ a * b := le_nonzero_prod_left h5
  have h7 : b ≤ a * b := le_nonzero_prod_right h5
  rewrite [←h3] at h6
  rewrite [←h3] at h7
  have h8 : b ≠ p := by
    contradict h4.left with h8
    rewrite [←one_mul p, h8] at h3
    have h9 : p > 0 := by linarith
    show a = 1 from Nat.eq_of_mul_eq_mul_right h9 h3.symm
    done
  have h9 : a < p := lt_of_le_of_ne h6 h4.right
  have h10 : b < p := lt_of_le_of_ne h7 h8
  show a < p ∧ b < p from And.intro h9 h10
  done

lemma rel_prime_of_prime_not_dvd {a p : Nat}
    (h1 : prime p) (h2 : ¬p ∣ a) : rel_prime a p := by
  have h3 : gcd a p ∣ a := gcd_dvd_left a p
  have h4 : gcd a p ∣ p := gcd_dvd_right a p
  have h5 : gcd a p = 1 ∨ gcd a p = p := dvd_prime h1 h4
  have h6 : gcd a p ≠ p := by
    contradict h2 with h6
    rewrite [h6] at h3
    show p ∣ a from h3
    done
  disj_syll h5 h6
  show rel_prime a p from h5
  done

theorem Theorem_7_2_3 {a b p : Nat}
    (h1 : prime p) (h2 : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  or_right with h3
  have h4 : rel_prime a p := rel_prime_of_prime_not_dvd h1 h3
  show p ∣ b from Theorem_7_2_2 h2 h4
  done

-- Finds smallest divisor of n that is ≥ n - k
def first_div_ge (n k : Nat) : Nat :=
  match k with
    | 0 => n
    | j + 1 => if n - (j + 1) ∣ n then n - (j + 1) else first_div_ge n j

lemma fdge_base (n : Nat) : first_div_ge n 0 = n := by rfl

lemma fdge_step (n j : Nat) :
    first_div_ge n (j + 1) =
      if n - (j + 1) ∣ n then n - (j + 1) else first_div_ge n j := by rfl

lemma fdge_dvd (n : Nat) : ∀ (k : Nat), first_div_ge n k ∣ n := by
  by_induc
  · -- Base Case
    rewrite [fdge_base]  --Goal : n ∣ n
    show n ∣ n from dvd_self n
    done
  · -- Induction Step
    fix k : Nat
    assume ih : first_div_ge n k ∣ n
    rewrite [fdge_step]  --Goal :
      -- (if n - (k + 1) ∣ n then n - (k + 1) else first_div_ge n k) ∣ n
    by_cases h1 : n - (k + 1) ∣ n
    · -- Case 1. h1 : n - (k + 1) ∣ n
      rewrite [if_pos h1]  --Goal : n - (k + 1) ∣ n
      show n - (k + 1) ∣ n from h1
      done
    · -- Case 2. h1 : ¬n - (k + 1) ∣ n
      rewrite [if_neg h1]  --Goal : first_div_ge n k ∣ n
      show first_div_ge n k ∣ n from ih
      done
    done
  done

lemma fdge_ge (n : Nat) : ∀ (k : Nat), n - k ≤ first_div_ge n k := by
  by_induc
  · -- Base Case
    rewrite [fdge_base]
    norm_num
    done
  · -- Induction Step
    fix k : Nat
    assume ih : n - k ≤ first_div_ge n k
    rewrite [fdge_step]
    by_cases h4 : n - (k + 1) ∣ n
    · -- Case 2.1. h4 : n - (k + 1) ∣ n
      rewrite [if_pos h4]
      linarith
      done
    · -- Case 2.2. h4 : ¬n - (k + 1) ∣ n
      rewrite [if_neg h4]
      have h5 : k ≤ k + 1 := by linarith
      have h6 : n - (k + 1) ≤ n - k := Nat.sub_le_sub_left n h5
      linarith
      done
    done
  done

lemma fdge_least (d n : Nat) : ∀ (k : Nat), d ∣ n → n - k ≤ d → first_div_ge n k ≤ d := by
  by_induc
  · -- Base Case
    rewrite [fdge_base]
    assume h1 : d ∣ n
    assume h2 : n - 0 ≤ d
    show n ≤ d from h2
    done
  · -- Induction Step
    fix k : Nat
    assume ih : d ∣ n → n - k ≤ d → first_div_ge n k ≤ d
    assume h1 : d ∣ n
    assume h2 : n - (k + 1) ≤ d
    rewrite [fdge_step]
    by_cases h3 : n - (k + 1) ∣ n
    · -- Case 1. h3 : n - (k + 1) ∣ n
      rewrite [if_pos h3]
      show n - (k + 1) ≤ d from h2
      done
    · -- Case 2. h3 : ¬n - (k + 1) ∣ n
      rewrite [if_neg h3]
      have h4 : d ≠ n - (k + 1) := by
        contradict h3 with h4
        rewrite [h4] at h1
        show n - (k + 1) ∣ n from h1
        done
      have h5 : n - k ≤ d :=
        calc n - k
          _ ≤ n - k - 1 + 1 := le_tsub_add
          _ = n - (k + 1) + 1 := by rfl 
          _ ≤ d := lt_of_le_of_ne' h2 h4
      show first_div_ge n k ≤ d from ih h1 h5
      done
    done
  done

def first_div (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | j + 2 => first_div_ge (j + 2) j
 
lemma fd_zero : first_div 0 = 0 := by rfl

lemma fd_one : first_div 1 = 1 := by rfl

lemma fd_plus_two (j : Nat) :
    first_div (j + 2) = first_div_ge (j + 2) j := by rfl

lemma fd_dvd (n : Nat) : first_div n ∣ n := by
  by_cases h1 : n = 0
  · -- Case 1. h1 : n = 0
    rewrite [h1, fd_zero]
    show 0 ∣ 0 from dvd_self 0
    done
  · -- Case 2. h1 : n ≠ 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2 : n = 1
      rewrite [h2, fd_one]
      show 1 ∣ 1 from dvd_self 1
      done
    · -- Case 2.2. h2 : n ≠ 1
      obtain (j : Nat) (h3 : n = j + 2) from plus_two_of_ne h1 h2
      rewrite [h3, fd_plus_two j]
      show first_div_ge (j + 2) j ∣ (j + 2) from fdge_dvd (j + 2) j
      done
    done
  done

lemma fd_nontriv (n : Nat) : first_div (n + 2) ≥ 2 :=
  calc first_div (n + 2)
    _ = first_div_ge (n + 2) n := by rw [fd_plus_two]
    _ ≥ n + 2 - n := fdge_ge (n + 2) n
    _ = 2 := Nat.add_sub_cancel_left n 2

lemma fd_least {n d : Nat} (h1 : d ∣ (n + 2)) (h2 : d ≥ 2) :
    first_div (n + 2) ≤ d := by
  rewrite [fd_plus_two]
  have h3 : n + 2 - n ≤ d :=
    calc n + 2 - n
      _ = 2 := Nat.add_sub_cancel_left n 2
      _ ≤ d := h2
  show first_div_ge (n + 2) n ≤ d from fdge_least d (n + 2) n h1 h3
  done

def first_codiv (n : Nat) : Nat := n / (first_div n)
 
lemma fc_mul_fd (n : Nat) : (first_codiv n) * (first_div n) = n :=
    Nat.div_mul_cancel (fd_dvd n)

lemma fd_mul_fc (n : Nat) : (first_div n) * (first_codiv n) = n := by
    rewrite [mul_comm]
    show (first_codiv n) * (first_div n) = n from fc_mul_fd n
    done

lemma fc_dvd (n : Nat) : first_codiv n ∣ n := by
  define
  apply Exists.intro (first_div n)
  show n = (first_codiv n) * (first_div n) from (fc_mul_fd n).symm
  done

theorem fd_prime (n : Nat) : prime (first_div (n + 2)) := by
  define
  apply And.intro (fd_nontriv n)
  by_contra h1
  obtain (a : Nat) (h2 : ∃ (b : Nat), a * b = first_div (n + 2) ∧
    a < first_div (n + 2) ∧ b < first_div (n + 2)) from h1
  obtain (b : Nat) (h3 : a * b = first_div (n + 2) ∧
    a < first_div (n + 2) ∧ b < first_div (n + 2)) from h2
  have h4 : a * b = first_div (n + 2) := h3.left
  have h5 : a ≠ 0 := by
    by_contra h5
    rewrite [h5] at h4
    have h6 : first_div (n + 2) ≥ 2 := fd_nontriv n
    linarith   --h4 contradicts h6
    done
  have h6 : a ≠ 1 := by
    by_contra h6
    rewrite [h6] at h4
    linarith   --h4 contradicts h3.right.right
    done
  have h7 : a ≥ 2 := ge_two_of_ne h5 h6
  have h8 : a ∣ (n + 2) := by
    define
    apply Exists.intro (b * (first_codiv (n + 2)))
    rewrite [←mul_assoc, h4]
    show n + 2 = first_div (n + 2) * first_codiv (n + 2) from
      (fd_mul_fc (n + 2)).symm
    done
  have h9 : first_div (n + 2) ≤ a := fd_least h8 h7
  linarith   --h9 contradicts h3.right.left
  done

lemma fc_dec (n : Nat) : first_codiv (n + 2) < n + 2 := by
  have h1 : 1 < first_div (n + 2) := fd_nontriv n
  have h2 : 0 < n + 2 := by linarith
  show first_codiv (n + 2) < n + 2 from Nat.div_lt_self h2 h1
  done

def prime_fac (n : Nat) : List Nat :=
  match n with
    | 0 => []
    | 1 => []
    | j + 2 => 
      have : first_codiv (j + 2) < j + 2 := fc_dec j
      first_div (j + 2) :: (prime_fac (first_codiv (j + 2)))

#eval prime_fac 276   --Answer: [2, 2, 3, 23]

lemma prime_fac_zero : prime_fac 0 = [] := by rfl

lemma prime_fac_one : prime_fac 1 = [] := by rfl

lemma prime_fac_step (j : Nat) : prime_fac (j + 2) =
    (first_div (j + 2)) :: prime_fac (first_codiv (j + 2)) := by rfl

def all_prime (l : List Nat) : Prop := ∀ (p : Nat), p ∈ l → prime p

lemma all_prime_nil : all_prime [] := by
  define     --Goal : ∀ (p : Nat), p ∈ [] → prime p
  fix p : Nat
  contrapos  --Goal : ¬prime p → ¬p ∈ []
  assume h1 : ¬prime p
  show ¬p ∈ [] from List.not_mem_nil p
  done

lemma all_prime_cons (n : Nat) (l : List Nat) :
    all_prime (n :: l) ↔ prime n ∧ all_prime l := by
  apply Iff.intro
  · -- (→)
    assume h1 : all_prime (n :: l)  --Goal : prime n ∧ all_prime l
    define at h1  --h1 : ∀ (p : Nat), p ∈ n :: l → prime p
    apply And.intro (h1 n (List.mem_cons_self n l))
    define        --Goal : ∀ (p : Nat), p ∈ l → prime p
    fix p : Nat
    assume h2 : p ∈ l
    show prime p from h1 p (List.mem_cons_of_mem n h2)
    done
  · -- (←)
    assume h1 : prime n ∧ all_prime l  --Goal : all_prime (n :: l)
    define : all_prime l at h1
    define
    fix p : Nat
    assume h2 : p ∈ n :: l
    rewrite [List.mem_cons] at h2   --h2 : p = n ∨ p ∈ l
    by_cases on h2
    · -- Case 1. h2 : p = n
      rewrite [h2]
      show prime n from h1.left
      done
    · -- Case 2. h2 : p ∈ l
      show prime p from h1.right p h2
      done
    done
  done

theorem prime_fac_all_prime : ∀ (n : Nat), all_prime (prime_fac n) := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n → all_prime (prime_fac n_1)
  by_cases h1 : n = 0
  · -- Case 1. h1 : n = 0
    rewrite [h1, prime_fac_zero]
    show all_prime [] from all_prime_nil
    done
  · -- Case 2. h1 : n ≠ 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2 : n = 1
      rewrite [h2, prime_fac_one]
      show all_prime [] from all_prime_nil
      done
    · -- Case 2.2. h2 : n ≠ 1
      obtain (j : Nat) (h3 : n = j + 2) from plus_two_of_ne h1 h2
      rewrite [h3, prime_fac_step, all_prime_cons]
      apply And.intro (fd_prime j)
      rewrite [h3] at ih
      show all_prime (prime_fac (first_codiv (j + 2))) from
        ih (first_codiv (j + 2)) (fc_dec j)
      done
    done
  done

def prod (l : List Nat) : Nat :=
  match l with
    | [] => 1
    | n :: L => n * (prod L)

lemma prod_nil : prod [] = 1 := by rfl

lemma prod_cons : prod (n :: l) = n * (prod l) := by rfl

lemma fc_ge_one (n : Nat) : first_codiv (n + 2) ≥ 1 := by
  have h1 := fd_mul_fc (n + 2)
  have h2 : first_codiv (n + 2) ≠ 0 := by
    by_contra h2
    rewrite [h2] at h1
    linarith
    done
  show first_codiv (n + 2) ≥ 1 from Nat.pos_of_ne_zero h2
  done

theorem prime_fac_prod : ∀ n ≥ 1, prod (prime_fac n) = n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n →
    n_1 ≥ 1 → prod (prime_fac n_1) = n_1
  assume h1 : n ≥ 1
  by_cases h2 : n = 1
  · -- Case 1. h2 : n = 1
    rewrite [h2, prime_fac_one, prod_nil]
    rfl
    done
  · -- Case 2. h2 : n ≠ 1
    have h3 : n ≥ 2 := lt_of_le_of_ne' h1 h2
    obtain (j : Nat) (h4 : n = j + 2) from plus_two_of_ge h3
    rewrite [h4, prime_fac_step, prod_cons]
    rewrite [h4] at ih
    have h5 : prod (prime_fac (first_codiv (j + 2))) =
        first_codiv (j + 2) :=
      ih (first_codiv (j + 2)) (fc_dec j) (fc_ge_one j)
    rewrite [h5]
    show first_div (j + 2) * first_codiv (j + 2) = j + 2 from
      fd_mul_fc (j + 2)
  done

def le_list (n : Nat) (l : List Nat) : Prop :=
  ∀ (m : Nat), m ∈ l → n ≤ m

def nondec (l : List Nat) : Prop :=
  match l with
    | [] => True   --Of course, True is a proposition that is always true
    | n :: L => le_list n L ∧ nondec L

lemma le_list_nil (n : Nat) : le_list n [] := by
  define
  fix m : Nat
  contrapos
  assume h : ¬n ≤ m
  show ¬m ∈ [] from List.not_mem_nil m
  done

lemma le_list_cons (n m : Nat) (l : List Nat) :
    le_list n (m :: l) ↔ n ≤ m ∧ le_list n l := by
  apply Iff.intro
  · -- (→)
    assume h1 : le_list n (m :: l)
    define at h1
    apply And.intro (h1 m (List.mem_cons_self m l))
    define
    fix k : Nat
    assume h2 : k ∈ l
    show n ≤ k from h1 k (List.mem_cons_of_mem m h2)
    done
  · -- (←)
    assume h1 : n ≤ m ∧ le_list n l
    define
    fix k : Nat
    assume h2 : k ∈ m :: l
    rewrite [List.mem_cons] at h2
    by_cases on h2
    · -- Case 1. h2 : k = m
      rewrite [h2]
      show n ≤ m from h1.left
      done
    · -- Case 2. h2 : k ∈ l
      show n ≤ k from h1.right k h2
      done
    done
  done

lemma nondec_nil : nondec [] := by
  define  --Goal : True
  trivial --trivial proves some obviously true statements, such as True
  done

lemma nondec_cons (n : Nat) (l : List Nat) :
    nondec (n :: l) ↔ le_list n l ∧ nondec l := by rfl

theorem dvd_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  define at h1; define at h2; define
  obtain (m : Nat) (h3 : b = a * m) from h1
  obtain (n : Nat) (h4 : c = b * n) from h2
  rewrite [h4, h3]
  apply Exists.intro (m * n)
  rewrite [mul_assoc]
  rfl
  done

lemma fd_le_prime_fac (n : Nat) : ∀ (k : Nat),
    k ∣ (n + 2) → le_list (first_div (n + 2)) (prime_fac k) := by
  by_strong_induc
  fix k : Nat
  assume ih : ∀ (k_1 : Nat), k_1 < k →
    k_1 ∣ n + 2 → le_list (first_div (n + 2)) (prime_fac k_1)
  assume h1 : k ∣ n + 2
  by_cases h2 : k = 0
  · -- Case 1. h2 : k = 0
    rewrite [h2, prime_fac_zero]
    show le_list (first_div (n + 2)) [] from le_list_nil _
    done
  · -- Case 2. h2 : k ≠ 0
    by_cases h3 : k = 1
    · -- Case 2.1. h3 : k = 1
      rewrite [h3, prime_fac_one]
      show le_list (first_div (n + 2)) [] from le_list_nil _
      done
    · -- Case 2.2. h3 : k ≠ 1
      obtain (j : Nat) (h4 : k = j + 2) from plus_two_of_ne h2 h3
      rewrite [h4, prime_fac_step, le_list_cons, ←h4]
      apply And.intro
      · -- Proof that first_div (n + 2) ≤ first_div k
        have h5 : first_div k ∣ k := fd_dvd k
        have h6 : first_div k ∣ (n + 2) := dvd_trans h5 h1
        have h7 : first_div (j + 2) ≥ 2 := fd_nontriv j
        rewrite [←h4] at h7
        show first_div (n + 2) ≤ first_div k from fd_least h6 h7
        done
      · -- Proof that le_list (first_div (n + 2)) (prime_fac (first_codiv k))
        have h5 : first_codiv (j + 2) < j + 2 := fc_dec j
        rewrite [←h4] at h5
        have h6 : first_codiv k ∣ k := fc_dvd k
        have h7 : first_codiv k ∣ (n + 2) := dvd_trans h6 h1
        show le_list (first_div (n + 2)) (prime_fac (first_codiv k)) from
          ih (first_codiv k) h5 h7
        done
      done
    done
  done

theorem prime_fac_nondec : ∀ (n : Nat), nondec (prime_fac n) := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n → nondec (prime_fac n_1)
  by_cases h1 : n = 0
  · -- Case 1. h1 : n = 0
    rewrite [h1, prime_fac_zero]
    show nondec [] from nondec_nil
    done
  · -- Case 2. h1 : n ≠ 0
    by_cases h2 : n = 1
    · -- Case 2.1. h2 : n = 1
      rewrite [h2, prime_fac_one]
      show nondec [] from nondec_nil
      done
    · -- Case 2.2. h2 : n ≠ 1
      obtain (j : Nat) (h3 : n = j + 2) from plus_two_of_ne h1 h2
      rewrite [h3, prime_fac_step, nondec_cons]
      apply And.intro
      · -- Proof that first_div n ≤ rest of list
        have h4 : first_codiv (j + 2) ∣ j + 2 := fc_dvd (j + 2)
        show le_list (first_div (j + 2))
          (prime_fac (first_codiv (j + 2))) from
          fd_le_prime_fac j (first_codiv (j + 2)) h4
        done
      · -- Proof that rest of list is nondecreasing
        have h4 : first_codiv (j + 2) < j + 2 := fc_dec j
        rewrite [h3] at ih
        show nondec (prime_fac (first_codiv (j + 2))) from
          ih (first_codiv (j + 2)) h4
      done
    done
  done

lemma ge_one_of_prod_one {a b : Nat} (h : a * b = 1) : a ≥ 1 := by
  have h1 : a ≠ 0 := by
    by_contra h1
    rewrite [h1] at h
    contradict h
    norm_num
    done
  show a ≥ 1 from Nat.pos_of_ne_zero h1
  done

lemma eq_one_of_prod_one {a b : Nat} (h : a * b = 1) : a = 1 := by
  have h1 : a ≥ 1 := ge_one_of_prod_one h
  have h2 : a * b ≠ 0 := by linarith
  have h3 : a ≤ a * b := le_nonzero_prod_left h2
  rewrite [h] at h3
  show a = 1 from Nat.le_antisymm h3 h1
  done

lemma eq_one_of_dvd_one {n : Nat} (h : n ∣ 1) : n = 1 := by
  obtain (j : Nat) (h1 : 1 = n * j) from h
  show n = 1 from eq_one_of_prod_one h1.symm
  done

lemma prime_not_one {p : Nat} (h : prime p) : p ≠ 1 := by
  define at h
  linarith
  done

lemma exists_cons_of_length_eq_succ
    {l : List Nat} {n : Nat} (h : l.length = n + 1) :
    ∃ (a : Nat) (L : List Nat), l = a :: L ∧ L.length = n := by
  have h1 : ¬l.length = 0 := by linarith
  rewrite [List.length_eq_zero] at h1
  obtain (a : Nat) (h2 : ∃ (L : List Nat), l = a :: L) from List.exists_cons_of_ne_nil h1
  obtain (L : List Nat) (h3 : l = a :: L) from h2
  apply Exists.intro a
  apply Exists.intro L
  apply And.intro h3
  have h4 : (a :: L).length = L.length + 1 := List.length_cons a L
  rewrite [←h3, h] at h4
  show L.length = n from (Nat.add_right_cancel h4).symm
  done

theorem Theorem_7_2_4_by_length {p : Nat} (h1 : prime p) :
    ∀ (k : Nat) (l : List Nat), l.length = k →
    p ∣ prod l → ∃ (a : Nat), a ∈ l ∧ p ∣ a := by
  by_induc
  · -- Base Case
    fix l : List Nat
    assume h2 : l.length = 0
    rewrite [List.length_eq_zero] at h2
    rewrite [h2, prod_nil]
    assume h3 : p ∣ 1
    show ∃ (a : Nat), a ∈ [] ∧ p ∣ a from
      absurd (eq_one_of_dvd_one h3) (prime_not_one h1)
    done
  · -- Induction Step
    fix k : Nat
    assume ih : ∀ (l : List Nat), l.length = k →
      p ∣ prod l → ∃ (a : Nat), a ∈ l ∧ p ∣ a
    fix l : List Nat
    assume h2 : l.length = k + 1
    obtain (a : Nat) (h3 : ∃ (L : List Nat),
      l = a :: L ∧ L.length = k) from exists_cons_of_length_eq_succ h2
    obtain (L : List Nat) (h4 : l = a :: L ∧ L.length = k) from h3
    rewrite [h4.left, prod_cons]
    assume h5 : p ∣ (a * prod L)
    have h6 : p ∣ a ∨ p ∣ prod L := Theorem_7_2_3 h1 h5
    by_cases on h6
    · -- Case 1. h6 : p ∣ a
      apply Exists.intro a
      show a ∈ a :: L ∧ p ∣ a from
        And.intro (List.mem_cons_self a L) h6
      done
    · -- Case 2. h6 : p ∣ prod L
      have h7 : ∃ (a : Nat), a ∈ L ∧ p ∣ a := ih L h4.right h6
      obtain (b : Nat) (h8 : b ∈ L ∧ p ∣ b) from h7
      apply Exists.intro b
      show b ∈ a :: L ∧ p ∣ b from
        And.intro (List.mem_cons_of_mem a h8.left) h8.right
      done
    done
  done

theorem Theorem_7_2_4 {p : Nat} {l : List Nat}
    (h1 : prime p) (h2 : p ∣ prod l) : ∃ (a : Nat), a ∈ l ∧ p ∣ a :=
  Theorem_7_2_4_by_length h1 l.length l (Eq.refl l.length) h2

lemma prime_in_list {p : Nat} {l : List Nat}
    (h1 : prime p) (h2 : all_prime l) (h3 : p ∣ prod l) : p ∈ l := by
  obtain (a : Nat) (h4 : a ∈ l ∧ p ∣ a) from Theorem_7_2_4 h1 h3
  define at h2
  have h5 : prime a := h2 a h4.left
  have h6 : p = 1 ∨ p = a := dvd_prime h5 h4.right
  disj_syll h6 (prime_not_one h1)
  rewrite [h6]
  show a ∈ l from h4.left
  done

def nondec_prime_list (l : List Nat) : Prop := all_prime l ∧ nondec l

lemma nondec_prime_list_tail {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : nondec_prime_list l := by
  define at h
  define
  rewrite [all_prime_cons, nondec_cons] at h
  show all_prime l ∧ nondec l from And.intro h.left.right h.right.right 
  done

lemma cons_prod_not_one {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : prod (p :: l) ≠ 1 := by
  define at h
  have h1 : all_prime (p :: l) := h.left
  rewrite [all_prime_cons] at h1
  rewrite [prod_cons]
  by_contra h2
  show False from (prime_not_one h1.left) (eq_one_of_prod_one h2)
  done

lemma list_nil_iff_prod_one {l : List Nat} (h : nondec_prime_list l) :
    l = [] ↔ prod l = 1 := by
  apply Iff.intro
  · -- (→)
    assume h1 : l = []
    rewrite [h1]
    show prod [] = 1 from prod_nil
    done
  · -- (←)
    contrapos
    assume h1 : ¬l = []
    obtain (p : Nat) (h2 : ∃ (L : List Nat), l = p :: L) from
      List.exists_cons_of_ne_nil h1
    obtain (L : List Nat) (h3 : l = p :: L) from h2
    rewrite [h3] at h
    rewrite [h3]
    show ¬prod (p :: L) = 1 from cons_prod_not_one h
    done
  done

lemma first_le_first {p q : Nat} {l m : List Nat}
    (h1 : nondec_prime_list (p :: l)) (h2 : nondec_prime_list (q :: m))
    (h3 : prod (p :: l) = prod (q :: m)) : p ≤ q := by
  define at h1; define at h2
  have h4 : q ∣ prod (p :: l) := by
    define
    apply Exists.intro (prod m)
    rewrite [←prod_cons]
    show prod (p :: l) = prod (q :: m) from h3
    done
  have h5 : all_prime (q :: m) := h2.left
  rewrite [all_prime_cons] at h5
  have h6 : q ∈ p :: l := prime_in_list h5.left h1.left h4
  have h7 : nondec (p :: l) := h1.right
  rewrite [nondec_cons] at h7
  rewrite [List.mem_cons] at h6
  by_cases on h6
  · -- Case 1. h6 : q = p
    show p ≤ q from Nat.le_of_eq h6.symm
    done
  · -- Case 2.  h6 : q ∈ l
    have h8 : le_list p l := h7.left
    define at h8
    show p ≤ q from h8 q h6
    done
  done

lemma prime_pos {p : Nat} (h : prime p) : p > 0 := by
  define at h
  linarith
  done

theorem Theorem_7_2_5 :
    ∀ (l1 l2 : List Nat), nondec_prime_list l1 → nondec_prime_list l2 →
    prod l1 = prod l2 → l1 = l2 := by
  apply List.rec
  · -- Base Case.  Goal : ∀ (l2 : List Nat), nondec_prime_list [] →
    -- nondec_prime_list l2 → prod [] = prod l2 → [] = l2
    fix l2 : List Nat
    assume h1 : nondec_prime_list []
    assume h2 : nondec_prime_list l2
    assume h3 : prod [] = prod l2
    rewrite [prod_nil, eq_comm, ←list_nil_iff_prod_one h2] at h3
    show [] = l2 from h3.symm
    done
  · -- Induction Step
    fix p : Nat
    fix L1 : List Nat
    assume ih : ∀ (L2 : List Nat), nondec_prime_list L1 →
      nondec_prime_list L2 → prod L1 = prod L2 → L1 = L2
    -- Goal : ∀ (l2 : List Nat), nondec_prime_list (p :: L1) →
    -- nondec_prime_list l2 → prod (p :: L1) = prod l2 → p :: L1 = l2
    fix l2 : List Nat
    assume h1 : nondec_prime_list (p :: L1)
    assume h2 : nondec_prime_list l2
    assume h3 : prod (p :: L1) = prod l2
    have h4 : ¬prod (p :: L1) = 1 := cons_prod_not_one h1
    rewrite [h3, ←list_nil_iff_prod_one h2] at h4
    obtain (q : Nat) (h5 : ∃ (L : List Nat), l2 = q :: L) from
      List.exists_cons_of_ne_nil h4
    obtain (L2 : List Nat) (h6 : l2 = q :: L2) from h5
    rewrite [h6] at h2    --h2 : nondec_prime_list (q :: L2)
    rewrite [h6] at h3    --h3 : prod (p :: L1) = prod (q :: L2)
    have h7 : p ≤ q := first_le_first h1 h2 h3
    have h8 : q ≤ p := first_le_first h2 h1 h3.symm
    have h9 : p = q := Nat.le_antisymm h7 h8
    rewrite [h9, prod_cons, prod_cons] at h3
    have h10 : nondec_prime_list L1 := nondec_prime_list_tail h1
    have h11 : nondec_prime_list L2 := nondec_prime_list_tail h2
    define at h2
    have h12 : all_prime (q :: L2) := h2.left
    rewrite [all_prime_cons] at h12
    have h13 : q > 0 := prime_pos h12.left
    have h14 : prod L1 = prod L2 := Nat.eq_of_mul_eq_mul_left h13 h3
    have h15 : L1 = L2 := ih L2 h10 h11 h14
    rewrite [h6, h9, h15]
    rfl
    done
  done

theorem Theorem_7_2_6_Fund_Thm_Arith (n : Nat) (h : n ≥ 1) :
    ∃! (l : List Nat), nondec_prime_list l ∧ prod l = n := by
  exists_unique
  · -- Existence
    apply Exists.intro (prime_fac n)
    have h1 : nondec_prime_list (prime_fac n) :=
      And.intro (prime_fac_all_prime n) (prime_fac_nondec n)
    show nondec_prime_list (prime_fac n) ∧ prod (prime_fac n) = n from
      And.intro h1 (prime_fac_prod n h)
    done
  · -- Uniqueness
    fix l1 : List Nat; fix l2 : List Nat
    assume h1 : nondec_prime_list l1 ∧ prod l1 = n
    assume h2 : nondec_prime_list l2 ∧ prod l2 = n
    have h3 : prod l1 = n := h1.right
    rewrite [←h2.right] at h3
    show l1 = l2 from Theorem_7_2_5 l1 l2 h1.left h2.left h3
    done
  done

/- Section 7.3 -/
def congr_mod (m : Nat) (a b : Int) : Prop := (↑m : Int) ∣ (a - b)

theorem congr_refl (m : Nat) : ∀ (a : Int), congr_mod m a a := by
  fix a : Int
  define                --Goal : ∃ (c : Int), a - a = ↑m * c
  apply Exists.intro 0
  norm_num
  done

theorem congr_symm {m : Nat} : ∀ {a b : Int},
    congr_mod m a b → congr_mod m b a := by
  fix a : Int; fix b : Int
  assume h1 : congr_mod m a b
  define at h1                 --h1 : ∃ (c : Int), a - b = ↑m * c
  define                       --Goal : ∃ (c : Int), b - a = ↑m * c
  obtain (c : Int) (h2 : a - b = m * c) from h1
  apply Exists.intro (-c)
  show b - a = m * (-c) from
    calc b - a
      _ = -(a - b) := by ring
      _ = -(m * c) := by rw [h2]
      _ = m * (-c) := by ring
  done

theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    congr_mod m a b → congr_mod m b c → congr_mod m a c := by
  fix a : Int; fix b : Int; fix c : Int
  assume h1 : congr_mod m a b
  assume h2 : congr_mod m b c
  obtain (d : Int) (h3 : a - b = m * d) from h1
  obtain (e : Int) (h4 : b - c = m * e) from h2
  apply Exists.intro (d + e)
  show a - c = m * (d + e) from
    calc a - c
      _ = (a - b) + (b - c) := by ring
      _ = m * d + m * e := by rw [h3, h4]
      _ = m * (d + e) := by ring
  done

/- Fundamental properties of congruence classes -/
def cc (m : Nat) (a : Int) : ZMod m := (↑a : ZMod m)

lemma cc_eq_iff_val_eq {n : Nat} (X Y : ZMod (n + 1)) :
    X = Y ↔ X.val = Y.val := Fin.eq_iff_veq X Y

lemma val_nat_eq_mod (n k : Nat) :
    (cc (n + 1) k).val = k % (n + 1) := by rfl

lemma val_zero (n : Nat) : (cc (n + 1) 0).val = 0 := by rfl

theorem cc_rep {m : Nat} (X : ZMod m) : ∃ (a : Int), X = cc m a :=
  match m with
    | 0 => by
      apply Exists.intro X
      rfl
      done
    | n + 1 => by
      apply Exists.intro ↑(X.val)
      have h1 : X.val < n + 1 := Fin.prop X
      rewrite [cc_eq_iff_val_eq, val_nat_eq_mod, Nat.mod_eq_of_lt h1]
      rfl
      done

theorem add_class (m : Nat) (a b : Int) :
    (cc m a) + (cc m b) = cc m (a + b) := (Int.cast_add a b).symm

theorem mul_class (m : Nat) (a b : Int) :
    (cc m a) * (cc m b) = cc m (a * b) := (Int.cast_mul a b).symm

lemma cc_eq_iff_sub_zero (m : Nat) (a b : Int) :
    cc m a = cc m b ↔ cc m (a - b) = cc m 0 := by
  apply Iff.intro
  · -- (→)
    assume h1 : cc m a = cc m b
    have h2 : a - b = a + (-b) := by ring
    have h3 : b + (-b) = 0 := by ring
    show cc m (a - b) = cc m 0 from
      calc cc m (a - b)
        _ = cc m (a + (-b)) := by rw [h2]
        _ = cc m a + cc m (-b) := by rw [add_class]
        _ = cc m b + cc m (-b) := by rw [h1]
        _ = cc m (b + -b) := by rw [add_class]
        _ = cc m 0 := by rw [h3]
    done
  · -- (←)
    assume h1 : cc m (a - b) = cc m 0
    have h2 : b + (a - b) = a := by ring
    have h3 : b + 0 = b := by ring
    show cc m a = cc m b from
      calc cc m a
        _ = cc m (b + (a - b)) := by rw [h2]
        _ = cc m b + cc m (a - b) := by rw [add_class]
        _ = cc m b + cc m 0 := by rw [h1]
        _ = cc m (b + 0) := by rw [add_class]
        _ = cc m b := by rw [h3]
    done
  done

lemma cc_neg_zero_of_cc_zero (m : Nat) (a : Int) :
    cc m a = cc m 0 → cc m (-a) = cc m 0 := by
  assume h1 : cc m a = cc m 0
  have h2 : 0 + -a = -a := by ring
  have h3 : a + (-a) = 0 := by ring
  show cc m (-a) = cc m 0 from
    calc cc m (-a)
      _ = cc m (0 + -a) := by rw [h2]
      _ = cc m 0 + cc m (-a) := by rw [add_class]
      _ = cc m a + cc m (-a) := by rw [h1]
      _ = cc m (a + (-a)) := by rw [add_class]
      _ = cc m 0 := by rw [h3]
  done

lemma cc_neg_zero_iff_cc_zero (m : Nat) (a : Int) :
    cc m (-a) = cc m 0 ↔ cc m a = cc m 0 := by
  apply Iff.intro _ (cc_neg_zero_of_cc_zero m a)
  assume h1 : cc m (-a) = cc m 0
  have h2 : cc m (-(-a)) = cc m 0 := cc_neg_zero_of_cc_zero m (-a) h1
  have h3 : -(-a) = a := by ring
  rewrite [h3] at h2
  show cc m a = cc m 0 from h2
  done

lemma cc_mod_0 (a : Int) : cc 0 a = a := by rfl

lemma cc_nat_zero_iff_dvd (m k : Nat) : cc m k = cc m 0 ↔ m ∣ k :=
  match m with
    | 0 => by
      have h : (0 : Int) = (↑(0 : Nat) : Int) := by rfl
      rewrite [cc_mod_0, cc_mod_0, h, @Nat.cast_inj Int]
      apply Iff.intro
      · -- (→)
        assume h1 : k = 0
        rewrite [h1]
        apply Exists.intro 0
        norm_num
        done
      · -- (←)
        assume h1 : 0 ∣ k
        obtain (c : Nat) (h2 : k = 0 * c) from h1
        rewrite [h2]
        norm_num
        done
      done
    | n + 1 => by
      rewrite [cc_eq_iff_val_eq, val_nat_eq_mod, val_zero]
      show k % (n + 1) = 0 ↔ n + 1 ∣ k from
        (Nat.dvd_iff_mod_eq_zero (n + 1) k).symm
      done

lemma cc_zero_iff_dvd (m : Nat) (a : Int) : cc m a = cc m 0 ↔ ↑m ∣ a := by
  obtain (k : Nat) (h1 : a = ↑k ∨ a = -↑k) from Int.eq_nat_or_neg a
  by_cases on h1
  · -- Case 1. h1: a = ↑k
    rewrite [h1, Int.coe_nat_dvd]
    show cc m ↑k = cc m 0 ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  · -- Case 2. h1: a = -↑k
    rewrite [h1, cc_neg_zero_iff_cc_zero, Int.dvd_neg, Int.coe_nat_dvd]
    show cc m ↑k = cc m 0 ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  done

theorem cc_eq_iff_congr (m : Nat) (a b : Int) :
    cc m a = cc m b ↔ congr_mod m a b :=
  calc cc m a = cc m b
    _ ↔ cc m (a - b) = cc m 0 := cc_eq_iff_sub_zero m a b
    _ ↔ ↑m ∣ (a - b) := cc_zero_iff_dvd m (a - b)
    _ ↔ congr_mod m a b := by rfl
/- End of fundamental properties of congruence classes -/

lemma mod_nonneg (m : Nat) [NeZero m] (a : Int) : 0 ≤ a % m := by
  have h1 : (↑m : Int) ≠ 0 := (Nat.cast_ne_zero).rtl (NeZero.ne m)
  show 0 ≤ a % m from Int.emod_nonneg a h1
  done

lemma mod_lt (m : Nat) [NeZero m] (a : Int) : a % m < m := by
  have h1 : m > 0 := Nat.pos_of_ne_zero (NeZero.ne m)
  have h2 : (↑m : Int) > 0 := (Nat.cast_pos).rtl h1
  show a % m < m from Int.emod_lt_of_pos a h2
  done

lemma congr_mod_mod (m : Nat) (a : Int) : congr_mod m a (a % m) := by
  define
  have h1 : m * (a / m) + a % m = a := Int.ediv_add_emod a m
  apply Exists.intro (a / m)
  show a - a % m = m * (a / m) from
    calc a - (a % m)
      _ = m * (a / m) + a % m - a % m := by rw [h1]
      _ = m * (a / m) := by ring
  done

lemma mod_cmpl_res (m : Nat) [NeZero m] (a : Int) :
    0 ≤ a % m ∧ a % m < m ∧ congr_mod m a (a % m) :=
  And.intro (mod_nonneg m a) (And.intro (mod_lt m a) (congr_mod_mod m a))

theorem Theorem_7_3_1 (m : Nat) [NeZero m] (a : Int) :
    ∃! (r : Int), 0 ≤ r ∧ r < m ∧ congr_mod m a r := by
  exists_unique
  · -- Existence
    apply Exists.intro (a % m)
    show 0 ≤ a % m ∧ a % m < m ∧ congr_mod m a (a % m) from mod_cmpl_res m a
    done
  · -- Uniqueness
    fix r1 : Int; fix r2 : Int
    assume h1 : 0 ≤ r1 ∧ r1 < m ∧ congr_mod m a r1
    assume h2 : 0 ≤ r2 ∧ r2 < m ∧ congr_mod m a r2
    have h3 : congr_mod m r1 r2 := congr_trans (congr_symm h1.right.right) h2.right.right
    obtain (d : Int) (h4 : r1 - r2 = m * d) from h3
    have h5 : r1 - r2 < m * 1 := by linarith
    have h6 : m * (-1) < r1 - r2 := by linarith
    rewrite [h4] at h5   --h5 : m * d < m * 1
    rewrite [h4] at h6   --h6 : m * -1 < m * d
    have h7 : (↑m : Int) ≥ 0 := Nat.cast_nonneg m
    have h8 : d < 1 := lt_of_mul_lt_mul_of_nonneg_left h5 h7
    have h9 : -1 < d := lt_of_mul_lt_mul_of_nonneg_left h6 h7
    have h10 : d = 0 := by linarith
    show r1 = r2 from
      calc r1
        _ = r1 - r2 + r2 := by ring
        _ = m * 0 + r2 := by rw [h4, h10]
        _ = r2 := by ring
    done
  done

lemma cc_eq_mod (m : Nat) (a : Int) : cc m a = cc m (a % m) := 
  (cc_eq_iff_congr m a (a % m)).rtl (congr_mod_mod m a)

--Can now prove all algebraic laws.  Examples:
theorem Theorem_7_3_6_1 {m : Nat} (X Y : ZMod m) : X + Y = Y + X := by
  obtain (a : Int) (h1 : X = cc m a) from cc_rep X
  obtain (b : Int) (h2 : Y = cc m b) from cc_rep Y
  rewrite [h1, h2]
  have h3 : a + b = b + a := by ring
  show cc m a + cc m b = cc m b + cc m a from
    calc cc m a + cc m b
      _ = cc m (a + b) := add_class m a b
      _ = cc m (b + a) := by rw [h3]
      _ = cc m b + cc m a := (add_class m b a).symm
  done

theorem Theorem_7_3_6_7 {m : Nat} (X : ZMod m) : X * cc m 1 = X := by
  obtain (a : Int) (h1 : X = cc m a) from cc_rep X
  rewrite [h1]
  have h2 : a * 1 = a := by ring
  show cc m a * cc m 1 = cc m a from
    calc cc m a * cc m 1
      _ = cc m (a * 1) := mul_class m a 1
      _ = cc m a := by rw [h2]
  done

def invertible {m : Nat} (X : ZMod m) : Prop :=
  ∃ (Y : ZMod m), X * Y = cc m 1

theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := by
  apply Iff.intro
  · -- (→)
    assume h1 : rel_prime a b
    define at h1
    apply Exists.intro (gcd_c1 a b)
    apply Exists.intro (gcd_c2 a b)
    have h2 : gcd_c1 a b * a + gcd_c2 a b * b = gcd a b :=
      gcd_lin_comb b a
    rewrite [h1, Nat.cast_one] at h2
    show gcd_c1 a b * a + gcd_c2 a b * b = 1 from h2
    done
  · -- (←)
    assume h1 : ∃ (s : Int), ∃ (t : Int), s * a + t * b = 1
    obtain (s : Int) (h2 : ∃ (t : Int), s * a + t * b = 1) from h1
    obtain (t : Int) (h3 : s * a + t * b = 1) from h2
    let g : Nat := gcd a b
    have h4 : g ∣ a := gcd_dvd_left a b
    have h5 : g ∣ b := gcd_dvd_right a b
    obtain (c : Nat) (h6 : a = g * c) from h4
    obtain (d : Nat) (h7 : b = g * d) from h5
    have h8 : g ∣ 1 := by
      rewrite [←Int.coe_nat_dvd, Nat.cast_one] --Goal : ↑g ∣ (1 : Int)
      apply Exists.intro (s * c + t * d)
      show 1 = g * (s * c + t * d) from
        calc 1
          _ = s * a + t * b := h3.symm
          _ = s * (g * c) + t * (g * d) := by
              rw [h6, h7, Nat.cast_mul, Nat.cast_mul]
          _ = g * (s * c + t * d) := by ring
      done
    define
    show gcd a b = 1 from eq_one_of_dvd_one h8
    done
  done

lemma gcd_c2_inv {m a : Nat} (h1 : rel_prime m a) :
    (cc m a) * (cc m (gcd_c2 m a)) = cc m 1 := by
  let s : Int := gcd_c1 m a
  have h2 : s * m + (gcd_c2 m a) * a = gcd m a := gcd_lin_comb a m
  define at h1
  rewrite [h1, Nat.cast_one] at h2
  rewrite [mul_class, cc_eq_iff_congr]
  define     --Goal : ∃ (c : Int), ↑a * gcd_c2 m a - 1 = ↑m * c
  apply Exists.intro (-s)
  show a * gcd_c2 m a - 1 = m * (-s) from
    calc a * (gcd_c2 m a) - 1
      _ = s * m + (gcd_c2 m a) * a + m * (-s) - 1 := by ring
      _ = 1 + m * (-s) - 1 := by rw [h2]
      _ = m * (-s) := by ring
  done

theorem Theorem_7_3_7 (m a : Nat) :
    invertible (cc m a) ↔ rel_prime m a := by
  apply Iff.intro
  · -- (→)
    assume h1 : invertible (cc m a)
    define at h1
    obtain (Y : ZMod m) (h2 : cc m a * Y = cc m 1) from h1
    obtain (b : Int) (h3 : Y = cc m b) from cc_rep Y
    rewrite [h3, mul_class, cc_eq_iff_congr] at h2
    define at h2
    obtain (c : Int) (h4 : a * b - 1 = m * c) from h2
    rewrite [Exercise_7_2_6]
      --Goal : ∃ (s t : Int), s * ↑m + t * ↑a = 1
    apply Exists.intro (-c)
    apply Exists.intro b
    show -c * m + b * a = 1 from
      calc (-c) * m + b * a
        _ = (-c) * m + (a * b - 1) + 1 := by ring
        _ = (-c) * m + m * c + 1 := by rw [h4]
        _ = 1 := by ring
    done
  · -- (←)
    assume h1 : rel_prime m a
    define
    show ∃ (Y : ZMod m), cc m a * Y = cc m 1 from
      Exists.intro (cc m (gcd_c2 m a)) (gcd_c2_inv h1)
    done
  done

/- Section 7.4 -/
def num_rp_below (m k : Nat) : Nat :=
  match k with
    | 0 => 0
    | j + 1 => if gcd m j = 1 then (num_rp_below m j) + 1
                else num_rp_below m j

lemma num_rp_below_base {m : Nat} :
    num_rp_below m 0 = 0 := by rfl

lemma num_rp_below_step_rp {m j : Nat} (h : rel_prime m j) :
    num_rp_below m (j + 1) = (num_rp_below m j) + 1 := by
  have h1 : num_rp_below m (j + 1) =
    if gcd m j = 1 then (num_rp_below m j) + 1
    else num_rp_below m j := by rfl
  define at h        --h : gcd m j = 1
  rewrite [h1, if_pos h]
  rfl
  done

lemma num_rp_below_step_not_rp {m j : Nat} (h : ¬rel_prime m j) :
    num_rp_below m (j + 1) = num_rp_below m j := by
  have h1 : num_rp_below m (j +1) =
    if gcd m j = 1 then (num_rp_below m j) + 1
    else num_rp_below m j := by rfl
  define at h
  rewrite [h1, if_neg h]
  rfl
  done

def phi (m : Nat) := num_rp_below m m

lemma phi_def (m : Nat) : phi m = num_rp_below m m := by rfl

#eval phi 600   --Answer: 160
#eval phi 10    --Answer: 4

lemma prod_inv_iff_inv {m : Nat} {X : ZMod m}
    (h1 : invertible X) (Y : ZMod m) :
    invertible (X * Y) ↔ invertible Y := by
  apply Iff.intro
  · -- (→)
    assume h2 : invertible (X * Y)
    obtain (Z : ZMod m) (h3 : X * Y * Z = cc m 1) from h2
    apply Exists.intro (X * Z)
    rewrite [←h3]  --Goal : Y * (X * Z) = X * Y * Z
    ring     --Note that ring can do algebra in ZMod m
    done
  · -- (←)
    assume h2 : invertible Y
    obtain (Xi : ZMod m) (h3 : X * Xi = cc m 1) from h1
    obtain (Yi : ZMod m) (h4 : Y * Yi = cc m 1) from h2
    apply Exists.intro (Xi * Yi)
    show (X * Y) * (Xi * Yi) = cc m 1 from
      calc X * Y * (Xi * Yi)
        _ = (X * Xi) * (Y * Yi) := by ring
        _ = cc m 1 * cc m 1 := by rw [h3, h4]
        _ = cc m 1 := Theorem_7_3_6_7 (cc m 1)
    done
  done

def F (m i : Nat) : ZMod m := if gcd m i = 1 then cc m i else cc m 1

lemma F_rp_def {m i : Nat} (h : rel_prime m i) :
    F m i = cc m i := by
  have h1 : F m i = if gcd m i = 1 then cc m i else cc m 1 := by rfl
  define at h      --h : gcd m i = 1
  rewrite [h1, if_pos h]
  rfl
  done

lemma F_not_rp_def {m i : Nat} (h : ¬rel_prime m i) :
    F m i = cc m 1 := by
  have h1 : F m i = if gcd m i = 1 then cc m i else cc m 1 := by rfl
  define at h
  rewrite [h1, if_neg h]
  rfl
  done

def prod_seq {m : Nat}
    (j k : Nat) (f : Nat → ZMod m) : ZMod m :=
  match j with
    | 0 => cc m 1
    | n + 1 => prod_seq n k f * f (k + n)

lemma prod_seq_base {m : Nat}
    (k : Nat) (f : Nat → ZMod m) : prod_seq 0 k f = cc m 1 := by rfl

lemma prod_seq_step {m : Nat}
    (n k : Nat) (f : Nat → ZMod m) :
    prod_seq (n + 1) k f = prod_seq n k f * f (k + n) := by rfl

lemma prod_seq_zero_step {m : Nat}
    (n : Nat) (f : Nat → ZMod m) :
    prod_seq (n + 1) 0 f = prod_seq n 0 f * f n := by
  rewrite [prod_seq_step, zero_add]
  rfl
  done

lemma prod_one {m : Nat}
    (k : Nat) (f : Nat → ZMod m) : prod_seq 1 k f = f k := by
  rewrite [prod_seq_step, prod_seq_base, add_zero, mul_comm, Theorem_7_3_6_7]
  rfl
  done

def G (m a i : Nat) : Nat := (a * i) % m

lemma G_def (m a i : Nat) : G m a i = (a * i) % m := by rfl

lemma cc_G (m a i : Nat) : cc m (G m a i) = (cc m a) * (cc m i) :=
  calc cc m (G m a i)
    _ = cc m ((a * i) % m) := by rfl
    _ = cc m (a * i) := (cc_eq_mod m (a * i)).symm
    _ = (cc m a) * (cc m i) := by rw [mul_class]

lemma G_rp_iff {m a : Nat} (h1 : rel_prime m a) (i : Nat) :
    rel_prime m (G m a i) ↔ rel_prime m i := by
  have h2 : invertible (cc m a) := (Theorem_7_3_7 m a).rtl h1
  show rel_prime m (G m a i) ↔ rel_prime m i from
    calc rel_prime m (G m a i)
      _ ↔ invertible (cc m (G m a i)) := (Theorem_7_3_7 m (G m a i)).symm
      _ ↔ invertible ((cc m a) * (cc m i)) := by rw [cc_G]
      _ ↔ invertible (cc m i) := prod_inv_iff_inv h2 (cc m i)
      _ ↔ rel_prime m i := Theorem_7_3_7 m i
  done

lemma FG_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : rel_prime m i) :
    F m (G m a i) = cc m a * F m i := by
  have h3 : rel_prime m (G m a i) := (G_rp_iff h1 i).rtl h2
  show F m (G m a i) = cc m a * F m i from
    calc F m (G m a i)
      _ = cc m (G m a i) := F_rp_def h3
      _ = cc m a * cc m i := cc_G m a i
      _ = cc m a * F m i := by rw [F_rp_def h2]
  done

lemma FG_not_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : ¬rel_prime m i) :
    F m (G m a i) = cc m 1 := by
  rewrite [←G_rp_iff h1 i] at h2
  show F m (G m a i) = cc m 1 from F_not_rp_def h2
  done

lemma FG_prod {m a : Nat} (h1 : rel_prime m a) :
    ∀ (k : Nat), prod_seq k 0 ((F m) ∘ (G m a)) =
      (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m) := by
  by_induc
  · -- Base Case
    show prod_seq 0 0 ((F m) ∘ (G m a)) =
          (cc m a) ^ (num_rp_below m 0) * prod_seq 0 0 (F m) from
      calc prod_seq 0 0 ((F m) ∘ (G m a))
        _ = cc m 1 := prod_seq_base _ _
        _ = (cc m a) ^ 0 * cc m 1 := by ring
        _ = (cc m a) ^ (num_rp_below m 0) * prod_seq 0 0 (F m) := by
              rw [num_rp_below_base, prod_seq_base]
    done
  · -- Induction Step
    fix k : Nat
    assume ih : prod_seq k 0 ((F m) ∘ (G m a)) =
      (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m)
    by_cases h2 : rel_prime m k
    · -- Case 1. h2 : rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          (cc m a) ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              (cc m a * F m k) := by rw [FG_rp h1 h2]
          _ = (cc m a) ^ ((num_rp_below m k) + 1) *
              ((prod_seq k 0 (F m)) * F m k) := by ring
          _ = (cc m a) ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_rp h2, prod_seq_zero_step]
      done
    · -- Case 2. h2 : ¬rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          (cc m a) ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = (cc m a) ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              (cc m 1) := by rw [FG_not_rp h1 h2]
          _ = (cc m a) ^ (num_rp_below m k) *
              (prod_seq k 0 (F m) * (cc m 1)) := by ring
          _ = (cc m a) ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_not_rp h2, prod_seq_zero_step,
                F_not_rp_def h2]
      done
    done
  done

--Permuting a product of congruence classes doesn't change product
def maps_below (n : Nat) (g : Nat → Nat) : Prop := ∀ i < n, g i < n

def one_one_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ i1 < n, ∀ i2 < n, g i1 = g i2 → i1 = i2

def onto_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ k < n, ∃ i < n, g i = k

def perm_below (n : Nat) (g : Nat → Nat) : Prop :=
  maps_below n g ∧ one_one_below n g ∧ onto_below n g

lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := by
  define
  fix i1; assume h2
  fix i2; assume h3
  assume h4
  exact
    calc i1
      _ = g' (g i1) := (h1 i1 h2).symm
      _ = g' (g i2) := by rw [h4]
      _ = i2 := h1 i2 h3
  done

lemma right_inv_onto_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g (g' i) = i) (h2 : maps_below n g') : onto_below n g := by
  define
  fix k
  assume h3
  apply Exists.intro (g' k)
  define at h2
  exact And.intro (h2 k h3) (h1 k h3)
  done

def inv_mod (m a : Nat) : Nat := Int.toNat ((gcd_c2 m a) % m)

lemma cc_mul_inv_mod_eq_one {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    cc m a * cc m (inv_mod m a) = cc m 1 := by
  have h2 : 0 ≤ (gcd_c2 m a) % m := mod_nonneg m (gcd_c2 m a)
  exact
    calc cc m a * cc m (inv_mod m a)
      _ = cc m a * cc m (Int.toNat ((gcd_c2 m a) % m)) := by rfl
      _ = cc m a * cc m ((gcd_c2 m a) % m) := by rw [Int.toNat_of_nonneg h2]
      _ = cc m a * cc m (gcd_c2 m a) := by rw [←cc_eq_mod]
      _ = cc m 1 := gcd_c2_inv h1
  done

lemma mul_mod_mod_eq_mul_mod (m a b : Nat) : (a * (b % m)) % m = (a * b) % m :=
  calc a * (b % m) % m
      = a % m * (b % m % m) % m := Nat.mul_mod _ _ _
    _ = a % m * (b % m) % m := by rw [Nat.mod_mod]
    _ = a * b % m := (Nat.mul_mod _ _ _).symm

lemma mod_mul_mod_eq_mul_mod (m a b : Nat) : (a % m * b) % m = (a * b) % m := by
  rewrite [mul_comm, mul_mod_mod_eq_mul_mod, mul_comm]
  rfl
  done

theorem congr_iff_mod_eq (m a b : Nat) [NeZero m] : congr_mod m a b ↔ a % m = b % m := by
  have h1 := mod_cmpl_res m a
  have h2 := mod_cmpl_res m b
  rewrite [Int.ofNat_mod_ofNat] at h1
  rewrite [Int.ofNat_mod_ofNat] at h2 
  apply Iff.intro
  · -- (→)
    assume h3
    have h4 := congr_trans h3 (h2.right.right)
    have h5 := And.intro h2.left (And.intro h2.right.left h4)
    obtain r h6 h7 from Theorem_7_3_1 m a
    have h8 := h7 ↑(a % m) ↑(b % m) h1 h5
    rewrite [Nat.cast_inj] at h8
    exact h8
    done
  · -- (→)
    assume h3
    rewrite [h3] at h1
    exact congr_trans h1.right.right (congr_symm h2.right.right)
    done
  done

lemma mul_inv_mod_cancel {m a i : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : i < m) : a * (inv_mod m a) * i % m = i := by
  have h3 : cc m a * cc m (inv_mod m a) = cc m ↑(1 : Nat) := cc_mul_inv_mod_eq_one h1
  rewrite [mul_class, cc_eq_iff_congr, ←Nat.cast_mul, congr_iff_mod_eq] at h3
  exact
    calc a * (inv_mod m a) * i % m
      _ = (a * inv_mod m a) % m * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = 1 % m * i % m := by rw [h3]
      _ = 1 * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = i % m := by rw [one_mul]
      _ = i := Nat.mod_eq_of_lt h2
  done

#eval inv_mod 1 1
#eval inv_mod 847 34
#eval (34 * 573) % 847
#eval inv_mod 847 35
#eval (35 * 823) % 847

def Ginv (m a i : Nat) : Nat := G m (inv_mod m a) i

lemma Ginv_def {m a i : Nat} : Ginv m a i = G m (inv_mod m a) i := by rfl

#check Nat.mod_eq_of_lt   --(h : a < b) : a % b = a
#check Nat.mul_mod   --(a b n : ℕ) : a * b % n = a % n * (b % n) % n
#check Nat.mod_mod   --(a n : ℕ) : a % n % n = a % n
#check mul_inv_mod_cancel

theorem Ginv_right_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) : ∀ i < m,
    G m a (Ginv m a i) = i := by
  fix i
  assume h2
  exact
    calc G m a (Ginv m a i)
      _ = a * ((inv_mod m a * i) % m) % m := by rfl
      _ = a * (inv_mod m a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc]
      _ = i := mul_inv_mod_cancel h1 h2
  done

lemma Ginv_left_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) : ∀ i < m,
    Ginv m a (G m a i) = i := by
  fix i
  assume h2
  exact
    calc Ginv m a (G m a i)
      _ = inv_mod m a * ((a * i) % m) % m := by rfl
      _ = inv_mod m a * (a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc, mul_comm (inv_mod m a)]
      _ = i := mul_inv_mod_cancel h1 h2
  done

#check Nat.mul_mod    --a * b % n = a % n * b % n
#check Nat.mod_mod    --a % n % n = a % n
#check Nat.mod_eq_of_lt  -- (a < b) a % b = a

lemma G_maps_below (m a : Nat) [NeZero m] : maps_below m (G m a) := by
  define
  fix i
  assume h1
  rewrite [G_def]
  exact mod_nonzero_lt (a * i) (NeZero.ne m)
  done

lemma Ginv_maps_below (m a : Nat) [NeZero m] : maps_below m (Ginv m a) := G_maps_below m (inv_mod m a)

lemma G_one_one_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) : one_one_below m (G m a) :=
  left_inv_one_one_below (Ginv_left_inv h1)

lemma G_onto_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) : onto_below m (G m a) :=
  right_inv_onto_below (Ginv_right_inv h1) (Ginv_maps_below m a)

lemma G_perm_below {m a : Nat} [NeZero m]
    (h1 : rel_prime m a) : perm_below m (G m a) :=
  And.intro (G_maps_below m a) (And.intro (G_one_one_below h1) (G_onto_below h1))

def swap (u v i : Nat) : Nat :=
  if i = u then v else if i = v then u else i

lemma swap_fst (u v : Nat) : swap u v u = v := by
  define : swap u v u
  have h : u = u := by rfl
  rewrite [if_pos h]
  rfl
  done

lemma swap_snd (u v : Nat) : swap u v v = u := by
  define : swap u v v
  by_cases h1 : v = u
  · -- Case 1. h1 : v = u
    rewrite [if_pos h1]
    exact h1
    done
  · -- Case 2. h1 : v ≠ u
    rewrite [if_neg h1]
    have h2 : v = v := by rfl
    rewrite [if_pos h2]
    rfl
    done
  done

lemma swap_other {u v i : Nat} (h1 : i ≠ u) (h2 : i ≠ v) : swap u v i = i := by
  define : swap u v i
  rewrite [if_neg h1, if_neg h2]
  rfl
  done

lemma swap_values (u v i : Nat) : swap u v i = v ∨ swap u v i = u ∨ swap u v i = i := by
  by_cases h1 : i = u
  · -- Case 1. h1 : i = u
    apply Or.inl
    rewrite [h1]
    exact swap_fst u v
    done
  · -- Case 2. h1 : i ≠ u
    apply Or.inr
    by_cases h2 : i = v
    · -- Case 2.1. h2 : i = v
      apply Or.inl
      rewrite [h2]
      exact swap_snd u v
      done
    · -- Case 2.2. h2 : i ≠ v
      apply Or.inr
      exact swap_other h1 h2
      done
    done
  done

lemma swap_maps_below {u v n : Nat} (h1 : u < n) (h2 : v < n) : maps_below n (swap u v) := by
  define
  fix i
  assume h3
  have h4 := swap_values u v i
  by_cases on h4
  · -- Case 1. h4 : swap u v i = v
    rewrite [h4]
    exact h2
    done
  · -- Case 2.
    by_cases on h4
    · -- Case 2.1. h4 : swap u v i = u
      rewrite [h4]
      exact h1
      done
    · -- Case 2.2. h4 : swap u v i = i
      rewrite [h4]
      exact h3
      done
    done
  done

lemma swap_swap (u v n : Nat) : ∀ i < n, swap u v (swap u v i) = i := by
  fix i
  assume h
  by_cases h1 : i = u
  · -- Case 1. h1 : i = u
    rewrite [h1, swap_fst, swap_snd]
    rfl
    done
  · -- Case 2. h1 : i ≠ u
    by_cases h2 : i = v
    · -- Case 2.1. h2 : i = v
      rewrite [h2, swap_snd, swap_fst]
      rfl
      done
    · -- Case 2.2. h2 : i ≠ v
      rewrite [swap_other h1 h2, swap_other h1 h2]
      rfl
      done
    done
  done

lemma swap_one_one_below (u v n) : one_one_below n (swap u v) :=
  left_inv_one_one_below (swap_swap u v n)

lemma swap_onto_below {u v n} (h1 : u < n) (h2 : v < n) : onto_below n (swap u v) :=
  right_inv_onto_below (swap_swap u v n) (swap_maps_below h1 h2)

lemma swap_perm_below {u v n} (h1 : u < n) (h2 : v < n) : perm_below n (swap u v) :=
  And.intro (swap_maps_below h1 h2) (And.intro (swap_one_one_below u v n) (swap_onto_below h1 h2))

lemma comp_perm_below {n : Nat} {f g : Nat → Nat} (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := by
  define; define at h1; define at h2
  apply And.intro
  · -- Proof of maps_below n (f ∘ g)
    have h3 := h1.left
    have h4 := h2.left
    define at h3; define at h4
    define
    fix i
    assume h5
    exact h3 (g i) (h4 i h5)
    done
  · -- Rest
    apply And.intro
    · -- Proof of one_one_below n (f ∘ g)
      have h3 := h1.right.left
      have h4 := h2.right.left
      define at h3; define at h4
      define
      fix i1; assume h5
      fix i2; assume h6
      assume h7
      have h8 := h2.left; define at h8
      have h9 := h3 (g i1) (h8 i1 h5) (g i2) (h8 i2 h6) h7
      exact h4 i1 h5 i2 h6 h9
      done
    · -- Proof of onto_below n (f ∘ g)
      have h3 := h1.right.right
      have h4 := h2.right.right
      define at h3; define at h4; define
      fix k
      assume h5
      obtain k' h6 from h3 k h5
      obtain i h7 from h4 k' h6.left
      apply Exists.intro i
      apply And.intro h7.left
      define : (f ∘ g) i
      rewrite [h7.right]
      exact h6.right
      done
    done
  done

lemma trivial_swap (u : Nat) : swap u u = id := by
  apply funext
  fix x
  by_cases h1 : x = u
  · -- Case 1. h1 : x = u
    rewrite [h1, swap_fst]
    rfl
    done
  · -- Case 2. h1 : x ≠ u
    rewrite [swap_other h1 h1]
    rfl
    done
  done

lemma prod_eq_fun {m : Nat} (f g : Nat → ZMod m) (k : Nat) :
    ∀ (n : Nat), (∀ (i : Nat), i < n → f (k + i) = g (k + i)) →
      prod_seq n k f = prod_seq n k g := by
  by_induc
  · -- Base Case
    assume h
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n
    assume ih
    assume h1
    have h2 : ∀ (i : Nat), i < n → f (k + i) = g (k + i) := by
      fix i
      assume h2
      have h3 : i < n + 1 := by linarith
      exact h1 i h3
      done
    have h3 := ih h2
    have h4 : n < n + 1 := Nat.lt_succ_self n
    rewrite [prod_seq_step, prod_seq_step, h3, h1 n h4]
    rfl
    done
  done

lemma comp_def {A B C : Type} (f : B → C) (g : A → B) (x : A) :
    (f ∘ g) x = f (g x) := by rfl

lemma swap_prod_eq_prod_between {m u n : Nat} (f : Nat → ZMod m) (h1 : u < n) :
    prod_seq (n - u - 1) (u + 1) (f ∘ swap u n) = prod_seq (n - u - 1) (u + 1) f := by
  have h2 : ∀ i < n - u - 1, (f ∘ swap u n) (u + 1 + i) = f (u + 1 + i) := by
    fix i
    assume h2
    have h3 : u + 1 + i ≠ u := by linarith
    have h4 : u + 1 + i ≠ n := by
      by_contra h4
      rewrite [←h4, add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h2
      linarith
      done
    rewrite [comp_def, swap_other h3 h4]
    rfl
  exact prod_eq_fun (f ∘ swap u n) f (u + 1) (n - u - 1) h2
  done

lemma swap_prod_eq_prod_below {m u n : Nat} (f : Nat → ZMod m) (h1 : u ≤ n) :
    prod_seq u 0 (f ∘ swap u n) = prod_seq u 0 f := by
  have h2 : ∀ (i : Nat), i < u → (f ∘ swap u n) (0 + i) = f (0 + i) := by
    fix i
    assume h2
    have h3 : 0 + i ≠ u := by linarith
    have h4 : 0 + i ≠ n := by linarith
    rewrite [comp_def, swap_other h3 h4]
    rfl
    done
  exact prod_eq_fun (f ∘ swap u n) f 0 u h2
  done

lemma break_prod {m : Nat} (n : Nat) (f : Nat → ZMod m) :
    ∀ (j : Nat), prod_seq (n + j) 0 f = prod_seq n 0 f * prod_seq j n f := by
  by_induc
  · -- Base Case
    have h : n + 0 = n := by rfl
    rewrite [prod_seq_base, h, Theorem_7_3_6_7]
    rfl
    done
  · -- Induction Step
    fix j
    assume ih
    rewrite [←add_assoc, prod_seq_zero_step, prod_seq_step, ih, mul_assoc]
    rfl
    done
  done

lemma break_prod_twice  {m u j n : Nat} (f : Nat → ZMod m) (h1 : u + 1 + j = n) :
    prod_seq (n + 1) 0 f = prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n := by
  have h2 := break_prod n f 1
  rewrite [prod_one] at h2
  have h3 := break_prod (u + 1) f j
  rewrite [h1] at h3
  have h4 := break_prod u f 1
  rewrite [prod_one] at h4
  rewrite [h3, h4] at h2
  exact h2
  done

lemma swap_prod_eq_prod {m u n : Nat} (f : Nat → ZMod m) (h1 : u ≤ n) :
    prod_seq (n + 1) 0 (f ∘ swap u n) = prod_seq (n + 1) 0 f := by
  by_cases h2 : u = n
  · -- Case 1. h2 : u = n
    rewrite [h2, trivial_swap n]
    rfl
    done
  · -- Case 2. h2 : ¬u = n
    have h3 : u < n := Nat.lt_of_le_of_ne h1 h2
    obtain (j : Nat) (h4 : u + 1 + j = n) from Nat.le.dest h3
    have h5 := break_prod_twice f h4
    have h6 := break_prod_twice (f ∘ swap u n) h4
    have h7 := swap_prod_eq_prod_below f h1
    have h8 := swap_prod_eq_prod_between f h3
    have h9 : n - u - 1 = j := by rw [←h4, add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    rewrite [h9] at h8
    define : (f ∘ swap u n) u at h6
    define : (f ∘ swap u n) n at h6
    rewrite [h7, h8, swap_fst, swap_snd] at h6
    rewrite [h5, h6]
    ring
    done
  done

lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := by
  define; define at h1
  have h1_1 := h1.left
  have h1_2 := h1.right.left
  have h1_3 := h1.right.right
  define at h1_1; define at h1_2; define at h1_3
  have h3 : n < n + 1 := Nat.lt_succ_self n
  apply And.intro
  · -- Proof of maps_below
    define
    fix i
    assume h4
    have h5 : i < n + 1 := by linarith
    have h6 := h1_1 i h5
    have h7 : g i ≠ n := by
      by_contra h7
      rewrite [←h2] at h7
      have h8 := h1_2 i h5 n h3 h7
      linarith
      done
    show g i < n from Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h6) h7
    done
  · -- Rest
    apply And.intro
    · -- Proof of one_one
      define
      fix i1; assume h4
      fix i2; assume h5
      assume h6
      have h7 : i1 < n + 1 := by linarith
      have h8 : i2 < n + 1 := by linarith
      exact h1_2 i1 h7 i2 h8 h6
      done
    · -- Proof of onto
      define
      fix k
      assume h4
      have h5 : k < n + 1 := by linarith
      obtain i h6 from h1_3 k h5
      apply Exists.intro i
      apply And.intro _ h6.right
      by_contra h7
      have h8 : i = n := by linarith
      rewrite [←h6.right, h8, h2] at h4
      linarith
      done
    done
  done

lemma perm_prod {m : Nat} (f : Nat → ZMod m) :
    ∀ (n : Nat), ∀ (g : Nat → Nat), perm_below n g →
      prod_seq n 0 f = prod_seq n 0 (f ∘ g) := by
  by_induc
  · -- Base Case
    fix g
    assume h1
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n
    assume ih
    fix g
    assume h1
    define at h1
    have h2 := h1.right.right
    define at h2
    have h3 := h2 n
    have h4 : n < n + 1 := Nat.lt_succ_self n
    obtain u h5 from h3 h4
    have h6 := swap_perm_below h5.left h4
    have h7 := comp_perm_below h1 h6
    have h8 : (g ∘ swap u n) n = n := by
      define : (g ∘ swap u n) n
      rewrite [swap_snd]
      exact h5.right
      done
    have h9 : perm_below n (g ∘ swap u n) := perm_below_fixed h7 h8
    have h10 := ih (g ∘ swap u n) h9
    have h11 : prod_seq (n + 1) 0 f = prod_seq (n + 1) 0 (f ∘ g ∘ swap u n) := by
      rewrite [prod_seq_zero_step, prod_seq_zero_step]
      rewrite [h10]
      define : (f ∘ g ∘ swap u n) n
      rewrite [h8]
      rfl
      done
    have h12 : u ≤ n := Nat.le_of_lt_succ h5.left
    have h13 := swap_prod_eq_prod (f ∘ g) h12
    have h14 : (f ∘ g) ∘ swap u n = f ∘ g ∘ swap u n := by rfl
    rewrite [h14, ←h11] at h13
    exact h13
    done
  done

lemma F_invertible (m i : Nat) : invertible (F m i) := by
  by_cases h : rel_prime m i
  · -- Case 1. h: rel_prime m i
    rewrite [F_rp_def h]
    show invertible (cc m i) from (Theorem_7_3_7 m i).rtl h
    done
  · -- Case 2. h: ¬rel_prime m i
    rewrite [F_not_rp_def h]
    apply Exists.intro (cc m 1)
    show cc m 1 * cc m 1 = cc m 1 from Theorem_7_3_6_7 (cc m 1)
  done

lemma Fprod_invertible (m : Nat) :
    ∀ (k : Nat), invertible (prod_seq k 0 (F m)) := by
  by_induc
  · -- Base Case
    apply Exists.intro (cc m 1)
    show prod_seq 0 0 (F m) * cc m 1 = cc m 1 from
      calc prod_seq 0 0 (F m) * cc m 1
        _ = cc m 1 * cc m 1 := by rw [prod_seq_base]
        _ = cc m 1 := Theorem_7_3_6_7 (cc m 1)
    done
  · -- Induction Step
    fix k : Nat
    assume ih : invertible (prod_seq k 0 (F m))
    rewrite [prod_seq_zero_step]
    show invertible (prod_seq k 0 (F m) * (F m k)) from
      (prod_inv_iff_inv ih (F m k)).rtl (F_invertible m k)
  done

--Euler's theorem for congruence classes
theorem Theorem_7_4_2 (m a : Nat) [NeZero m] (h1 : rel_prime m a) :
    (cc m a) ^ (phi m) = cc m 1 := by
  have h2 : invertible (prod_seq m 0 (F m)) := Fprod_invertible m m
  obtain (Y : ZMod m) (h3 : prod_seq m 0 (F m) * Y = cc m 1) from h2
  show (cc m a) ^ (phi m) = cc m 1 from
    calc (cc m a) ^ (phi m)
      _ = (cc m a) ^ (phi m) * cc m 1 := (Theorem_7_3_6_7 _).symm
      _ = (cc m a) ^ (phi m) * (prod_seq m 0 (F m) * Y) := by rw [h3]
      _ = ((cc m a) ^ (phi m) * prod_seq m 0 (F m)) * Y := by ring
      _ = prod_seq m 0 (F m ∘ G m a) * Y := by rw [FG_prod h1 m, phi_def]
      _ = prod_seq m 0 (F m) * Y := by
            rw [perm_prod (F m) m (G m a) (G_perm_below h1)]
      _ = cc m 1 := by rw [h3]
  done

--When state as exercise, give hint for base case:
--Use ring to prove (cc m ↑a) ^ 0 = (1 : ZMod m)
--Use Int.cast_one to prove cc m 1 = (1 : ZMod m)
lemma Exercise_7_4_5 (m a : Nat) :
    ∀ (n : Nat), (cc m a) ^ n = cc m (a ^ n) := by
  by_induc
  · -- Base Case
    show (cc m a) ^ 0 = cc m ↑(a ^ 0) from
      calc (cc m a) ^ 0
        _ = (1 : ZMod m) := by ring
        _ = cc m 1 := Int.cast_one.symm
        _ = cc m ↑(a ^ 0) := by rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (cc m a) ^ n = cc m ↑(a ^ n)
    show (cc m a) ^ (n + 1) = cc m ↑(a ^ (n + 1)) from
      calc (cc m a) ^ (n + 1)
        _ = (cc m a) ^ n * cc m a := by ring
        _ = cc m ↑(a ^ n) * cc m a := by rw [ih]
        _ = cc m (↑(a ^ n) * a) := mul_class _ _ _
        _ = cc m (↑(a ^ n * a)) := by rw [Nat.cast_mul]
        _ = cc m ↑(a ^ (n + 1)) := by rfl
    done
  done

theorem Theorem_7_4_3_Euler's_theorem (m a : Nat) [NeZero m]
    (h1 : rel_prime m a) : congr_mod m (a ^ (phi m)) 1 := by
  have h2 : (cc m a) ^ (phi m) = cc m 1 := Theorem_7_4_2 m a h1
  rewrite [Exercise_7_4_5 m a (phi m)] at h2
    --h2 : cc m ↑(a ^ phi m) = cc m 1
  show congr_mod m (a ^ (phi m)) 1 from (cc_eq_iff_congr _ _ _).ltr h2
  done

#eval gcd 10 7     --Answer: 1.  So 10 and 7 are relatively prime
#eval 7 ^ phi 10   --Answer: 2401, which is congruent to 1 mod 10.

/- Section 7.5 -/
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ (k : Nat), k < p → num_rp_below p (k + 1) = k := by
  by_induc
  · -- Base Case
    assume h2
    have h3 : ¬rel_prime p 0 := by
      define
      rewrite [gcd_base]
      exact prime_not_one h1
      done
    rewrite [num_rp_below_step_not_rp h3, num_rp_below_base]
    rfl
    done
  · -- Induction Step
    fix k
    assume ih
    assume h2
    have h3 : k < p := by linarith
    have h4 : rel_prime p (k + 1) := by
      define
      by_contra h4
      have h5 : gcd p (k + 1) ∣ p := gcd_dvd_left p (k + 1)
      have h6 : gcd p (k + 1) ∣ k + 1 := gcd_dvd_right p (k + 1)
      have h7 : gcd p (k + 1) = 1 ∨ gcd p (k + 1) = p := dvd_prime h1 h5
      disj_syll h7 h4
      rewrite [h7] at h6
      obtain j h8 from h6
      have h9 : j ≠ 0 := by
        by_contra h9
        rewrite [h9] at h8
        linarith
        done
      have h10 : j ≥ 1 := Nat.pos_of_ne_zero h9
      have h11 : k + 1 ≥ p :=
        calc k + 1
          _ = p * j := h8
          _ ≥ p * 1 := Nat.mul_le_mul_of_nonneg_left h10
          _ = p := mul_one _
      linarith
      done
    rewrite [num_rp_below_step_rp h4, ih h3]
    rfl
    done
  done

lemma phi_prime {p : Nat} (h1 : prime p) : phi p = p - 1 := by
  have h2 : 1 ≤ p := prime_pos h1
  have h3 : p - 1 + 1 = p := Nat.sub_add_cancel h2
  have h4 : p - 1 < p := by linarith
  have h5 : num_rp_below p (p - 1 + 1) = p - 1 := num_rp_prime h1 (p - 1) h4
  rewrite [h3] at h5
  define : phi p
  exact h5
  done
