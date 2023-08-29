/- Copyright 2023 Daniel J. Velleman -/

import Chap6
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

/- Definitions -/
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

def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n

def prime_factor (p n : Nat) : Prop := prime p ∧ p ∣ n

def all_prime (l : List Nat) : Prop := ∀ (p : Nat), p ∈ l → prime p

def nondec (l : List Nat) : Prop :=
  match l with
    | [] => True   --Of course, True is a proposition that is always true
    | n :: L => (∀ (m : Nat), m ∈ L → n ≤ m) ∧ nondec L

def nondec_prime_list (l : List Nat) : Prop := all_prime l ∧ nondec l

def prod (l : List Nat) : Nat :=
  match l with
    | [] => 1
    | n :: L => n * (prod L)

def prime_factorization (n : Nat) (l : List Nat) : Prop :=
  nondec_prime_list l ∧ prod l = n

def rel_prime (a b : Nat) : Prop := gcd a b = 1

def congr_mod (m : Nat) (a b : Int) : Prop := (↑m : Int) ∣ (a - b)

def cc (m : Nat) (a : Int) : ZMod m := (↑a : ZMod m)

notation:50 a " ≡ " b " (MOD " m ")" => congr_mod m a b

notation:max "["a"]_"m:max => cc m a

def invertible {m : Nat} (X : ZMod m) : Prop :=
  ∃ (Y : ZMod m), X * Y = [1]_m

def num_rp_below (m k : Nat) : Nat :=
  match k with
    | 0 => 0
    | j + 1 => if gcd m j = 1 then (num_rp_below m j) + 1
                else num_rp_below m j

def phi (m : Nat) := num_rp_below m m

def prod_seq {m : Nat}
    (j k : Nat) (f : Nat → ZMod m) : ZMod m :=
  match j with
    | 0 => [1]_m
    | n + 1 => prod_seq n k f * f (k + n)

def maps_below (n : Nat) (g : Nat → Nat) : Prop := ∀ i < n, g i < n

def one_one_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ i1 < n, ∀ i2 < n, g i1 = g i2 → i1 = i2

def onto_below (n : Nat) (g : Nat → Nat) : Prop :=
  ∀ k < n, ∃ i < n, g i = k

def perm_below (n : Nat) (g : Nat → Nat) : Prop :=
  maps_below n g ∧ one_one_below n g ∧ onto_below n g

def inv_mod (m a : Nat) : Nat := Int.toNat ((gcd_c2 m a) % m)

def swap (u v i : Nat) : Nat :=
  if i = u then v else if i = v then u else i

namespace Euler  --For definitions specific to Euler's theorem

def F (m i : Nat) : ZMod m := if gcd m i = 1 then [i]_m else [1]_m

def G (m a i : Nat) : Nat := (a * i) % m

def Ginv (m a i : Nat) : Nat := G m (inv_mod m a) i

end Euler

/- Section 7.1 -/
theorem dvd_mod_of_dvd_a_b {a b d : Nat}
    (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a % b) := by
  set q : Nat := a / b
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
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := sorry

#eval gcd 672 161    --Answer: 7

lemma gcd_base (a : Nat) : gcd a 0 = a := by rfl

lemma gcd_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd a b = gcd b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
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
    rewrite [gcd_nonzero a h1]
      --Goal : gcd b (a % b) ∣ a ∧ gcd b (a % b) ∣ b
    have h2 : a % b < b := mod_nonzero_lt a h1
    have h3 : (gcd b (a % b)) ∣ b ∧ (gcd b (a % b)) ∣ (a % b) :=
      ih (a % b) h2 b
    apply And.intro _ h3.left
    show (gcd b (a % b)) ∣ a from dvd_a_of_dvd_b_mod h3.left h3.right
    done
  done

theorem gcd_dvd_left (a b : Nat) : (gcd a b) ∣ a := (gcd_dvd b a).left

theorem gcd_dvd_right (a b : Nat) : (gcd a b) ∣ b := (gcd_dvd b a).right

lemma gcd_c1_base (a : Nat) : gcd_c1 a 0 = 1 := by rfl

lemma gcd_c1_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c1 a b = gcd_c2 b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rewrite [h2]
  rfl
  done

lemma gcd_c2_base (a : Nat) : gcd_c2 a 0 = 0 := by rfl

lemma gcd_c2_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c2 a b = gcd_c1 b (a % b) - (gcd_c2 b (a % b)) * ↑(a / b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
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
    rewrite [gcd_c1_nonzero a h1, gcd_c2_nonzero a h1, gcd_nonzero a h1]
      --Goal : gcd_c2 b (a % b) * ↑a +
      -- (gcd_c1 b (a % b) - gcd_c2 b (a % b) * ↑(a / b)) * ↑b =
      -- ↑(gcd b (a % b))
    set r : Nat := a % b
    set q : Nat := a / b
    set s : Int := gcd_c1 b r
    set t : Int := gcd_c2 b r
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
  set s : Int := gcd_c1 a b
  set t : Int := gcd_c2 a b
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
theorem dvd_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  define at h1; define at h2; define
  obtain (m : Nat) (h3 : b = a * m) from h1
  obtain (n : Nat) (h4 : c = b * n) from h2
  rewrite [h3, mul_assoc] at h4
  apply Exists.intro (m * n)
  show c = a * (m * n) from h4
  done

lemma exists_prime_factor : ∀ (n : Nat), 2 ≤ n →
    ∃ (p : Nat), prime_factor p n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n →
    2 ≤ n_1 → ∃ (p : Nat), prime_factor p n_1
  assume h1 : 2 ≤ n
  by_cases h2 : prime n
  · -- Case 1. h2 : prime n
    apply Exists.intro n
    define            --Goal : prime n ∧ n ∣ n
    show prime n ∧ n ∣ n from And.intro h2 (dvd_self n)
    done
  · -- Case 2. h2 : ¬prime n
    define at h2
      --h2 : ¬(2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n)
    demorgan at h2
    disj_syll h2 h1
    obtain (a : Nat) (h3 : ∃ (b : Nat), a * b = n ∧ a < n ∧ b < n) from h2
    obtain (b : Nat) (h4 : a * b = n ∧ a < n ∧ b < n) from h3
    have h5 : 2 ≤ a := by
      by_contra h6
      have h7 : a ≤ 1 := by linarith
      have h8 : n ≤ b :=
        calc n
          _ = a * b := h4.left.symm
          _ ≤ 1 * b := by rel [h7]
          _ = b := by ring
      linarith        --n ≤ b contradicts b < n
      done
    have h6 : ∃ (p : Nat), prime_factor p a := ih a h4.right.left h5
    obtain (p : Nat) (h7 : prime_factor p a) from h6
    apply Exists.intro p
    define            --Goal : prime p ∧ p ∣ n
    define at h7      --h7 : prime p ∧ p ∣ a
    apply And.intro h7.left
    have h8 : a ∣ n := by
      apply Exists.intro b
      show n = a * b from (h4.left).symm
      done
    show p ∣ n from dvd_trans h7.right h8
    done
  done

lemma exists_least_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q := by
  set S : Set Nat := { p : Nat | prime_factor p n }
  have h2 : ∃ (p : Nat), p ∈ S := exists_prime_factor n h
  show ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q from well_ord_princ S h2
  done

lemma all_prime_nil : all_prime [] := by
  define     --Goal : ∀ (p : Nat), p ∈ [] → prime p
  fix p : Nat
  contrapos  --Goal : ¬prime p → ¬p ∈ []
  assume h1 : ¬prime p
  show ¬p ∈ [] from List.not_mem_nil p
  done

lemma all_prime_cons (n : Nat) (L : List Nat) :
    all_prime (n :: L) ↔ prime n ∧ all_prime L := by
  apply Iff.intro
  · -- (→)
    assume h1 : all_prime (n :: L)  --Goal : prime n ∧ all_prime L
    define at h1  --h1 : ∀ (p : Nat), p ∈ n :: L → prime p
    apply And.intro (h1 n (List.mem_cons_self n L))
    define        --Goal : ∀ (p : Nat), p ∈ L → prime p
    fix p : Nat
    assume h2 : p ∈ L
    show prime p from h1 p (List.mem_cons_of_mem n h2)
    done
  · -- (←)
    assume h1 : prime n ∧ all_prime L  --Goal : all_prime (n :: l)
    define : all_prime L at h1
    define
    fix p : Nat
    assume h2 : p ∈ n :: L
    rewrite [List.mem_cons] at h2   --h2 : p = n ∨ p ∈ L
    by_cases on h2
    · -- Case 1. h2 : p = n
      rewrite [h2]
      show prime n from h1.left
      done
    · -- Case 2. h2 : p ∈ L
      show prime p from h1.right p h2
      done
    done
  done

lemma nondec_nil : nondec [] := by
  define  --Goal : True
  trivial --trivial proves some obviously true statements, such as True
  done

lemma nondec_cons (n : Nat) (L : List Nat) :
    nondec (n :: L) ↔ (∀ (m : Nat), m ∈ L → n ≤ m) ∧ nondec L := by rfl

lemma prod_nil : prod [] = 1 := by rfl

lemma prod_cons : prod (n :: L) = n * (prod L) := by rfl

lemma exists_cons_of_length_eq_succ {A : Type}
    {l : List A} {n : Nat} (h : l.length = n + 1) :
    ∃ (a : A) (L : List A), l = a :: L ∧ L.length = n := by
  have h1 : ¬l.length = 0 := by linarith
  rewrite [List.length_eq_zero] at h1
  obtain (a : A) (h2 : ∃ (L : List A), l = a :: L) from
    List.exists_cons_of_ne_nil h1
  obtain (L : List A) (h3 : l = a :: L) from h2
  apply Exists.intro a
  apply Exists.intro L
  apply And.intro h3
  have h4 : (a :: L).length = L.length + 1 := List.length_cons a L
  rewrite [←h3, h] at h4
  show L.length = n from (Nat.add_right_cancel h4).symm
  done

lemma list_elt_dvd_prod_by_length (a : Nat) : ∀ (n : Nat),
    ∀ (l : List Nat), l.length = n → a ∈ l → a ∣ prod l := by
  by_induc
  · --Base Case
    fix l : List Nat
    assume h1 : l.length = 0
    rewrite [List.length_eq_zero] at h1     --h1 : l = []
    rewrite [h1]                            --Goal : a ∈ [] → a ∣ prod []
    contrapos
    assume h2 : ¬a ∣ prod []
    show ¬a ∈ [] from List.not_mem_nil a
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (l : List Nat), List.length l = n → a ∈ l → a ∣ prod l
    fix l : List Nat
    assume h1 : l.length = n + 1            --Goal : a ∈ l → a ∣ prod l
    obtain (b : Nat) (h2 : ∃ (L : List Nat),
      l = b :: L ∧ L.length = n) from exists_cons_of_length_eq_succ h1
    obtain (L : List Nat) (h3 : l = b :: L ∧ L.length = n) from h2
    have h4 : a ∈ L → a ∣ prod L := ih L h3.right
    assume h5 : a ∈ l
    rewrite [h3.left, prod_cons]            --Goal : a ∣ b * prod L
    rewrite [h3.left, List.mem_cons] at h5  --h5 : a = b ∨ a ∈ L
    by_cases on h5
    · -- Case 1. h5 : a = b
      apply Exists.intro (prod L)
      rewrite [h5]
      rfl
      done
    · -- Case 2. h5 : a ∈ L
      have h6 : a ∣ prod L := h4 h5
      have h7 : prod L ∣ b * prod L := by
        apply Exists.intro b
        ring
        done
      show a ∣ b * prod L from dvd_trans h6 h7
      done
    done
  done

lemma list_elt_dvd_prod {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ∣ prod l := by
  set n : Nat := l.length
  have h1 : l.length = n := by rfl
  show a ∣ prod l from list_elt_dvd_prod_by_length a n l h1 h
  done

lemma exists_prime_factorization : ∀ (n : Nat), n ≥ 1 →
    ∃ (l : List Nat), prime_factorization n l := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n_1 : Nat), n_1 < n →
    n_1 ≥ 1 → ∃ (l : List Nat), prime_factorization n_1 l
  assume h1 : n ≥ 1
  by_cases h2 : n = 1
  · -- Case 1. h2 : n = 1
    apply Exists.intro []
    define
    apply And.intro
    · -- Proof of nondec_prime_list []
      define
      show all_prime [] ∧ nondec [] from
        And.intro all_prime_nil nondec_nil
      done
    · -- Proof of prod [] = n
      rewrite [prod_nil, h2]
      rfl
      done
    done
  · -- Case 2. h2 : n ≠ 1
    have h3 : n ≥ 2 := lt_of_le_of_ne' h1 h2
    obtain (p : Nat) (h4 : prime_factor p n ∧ ∀ (q : Nat),
      prime_factor q n → p ≤ q) from exists_least_prime_factor h3
    have p_prime_factor : prime_factor p n := h4.left
    define at p_prime_factor
    have p_prime : prime p := p_prime_factor.left
    have p_dvd_n : p ∣ n := p_prime_factor.right
    have p_least : ∀ (q : Nat), prime_factor q n → p ≤ q := h4.right
    obtain (m : Nat) (n_eq_pm : n = p * m) from p_dvd_n
    have h5 : m ≠ 0 := by
      contradict h1 with h6
      have h7 : n = 0 :=
        calc n
          _ = p * m := n_eq_pm
          _ = p * 0 := by rw [h6]
          _ = 0 := by ring
      rewrite [h7]
      norm_num
      done
    have m_pos : 0 < m := Nat.pos_of_ne_zero h5
    have m_lt_n : m < n := by
      define at p_prime
      show m < n from
        calc m
          _ < m + m := by linarith
          _ = 2 * m := by ring
          _ ≤ p * m := by rel [p_prime.left]
          _ = n := n_eq_pm.symm
      done
    obtain (L : List Nat) (h6 : prime_factorization m L)
      from ih m m_lt_n m_pos
    define at h6
    have ndpl_L : nondec_prime_list L := h6.left
    define at ndpl_L
    apply Exists.intro (p :: L)
    define
    apply And.intro
    · -- Proof of nondec_prime_list (p :: L)
      define
      apply And.intro
      · -- Proof of all_prime (p :: L)
        rewrite [all_prime_cons]
        show prime p ∧ all_prime L from And.intro p_prime ndpl_L.left
        done
      · -- Proof of nondec (p :: L)
        rewrite [nondec_cons]
        apply And.intro _ ndpl_L.right
        fix q : Nat
        assume q_in_L : q ∈ L
        have h7 : q ∣ prod L := list_elt_dvd_prod q_in_L
        rewrite [h6.right] at h7   --h7 : q ∣ m
        have h8 : m ∣ n := by
          apply Exists.intro p
          rewrite [n_eq_pm]
          ring
          done
        have q_dvd_n : q ∣ n := dvd_trans h7 h8
        have ap_L : all_prime L := ndpl_L.left
        define at ap_L
        have q_prime_factor : prime_factor q n :=
          And.intro (ap_L q q_in_L) q_dvd_n
        show p ≤ q from p_least q q_prime_factor
        done
      done
    · -- Proof of prod (p :: L) = n
      rewrite [prod_cons, h6.right, n_eq_pm]
      rfl
      done
    done
  done

theorem Theorem_7_2_2 {a b c : Nat}
    (h1 : c ∣ a * b) (h2 : rel_prime a c) : c ∣ b := by
  rewrite [←Int.coe_nat_dvd]  --Goal : ↑c ∣ ↑b
  define at h1; define at h2; define
  obtain (j : Nat) (h3 : a * b = c * j) from h1
  set s : Int := gcd_c1 a c
  set t : Int := gcd_c2 a c
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
      _ ≤ a * b := by rel [h2]
  done

lemma le_nonzero_prod_right {a b : Nat} (h : a * b ≠ 0) : b ≤ a * b := by
  rewrite [mul_comm]
  rewrite [mul_comm] at h
  show b ≤ b * a from le_nonzero_prod_left h
  done

lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

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

theorem Theorem_7_2_4 {p : Nat} (h1 : prime p) :
    ∀ (l : List Nat), p ∣ prod l → ∃ (a : Nat), a ∈ l ∧ p ∣ a := by
  apply List.rec
  · -- Base Case.  Goal : p ∣ prod [] → ∃ (a : Nat), a ∈ [] ∧ p ∣ a
    rewrite [prod_nil]
    assume h2 : p ∣ 1
    show ∃ (a : Nat), a ∈ [] ∧ p ∣ a from
      absurd (eq_one_of_dvd_one h2) (prime_not_one h1)
    done
  · -- Induction Step
    fix b : Nat
    fix L : List Nat
    assume ih : p ∣ prod L → ∃ (a : Nat), a ∈ L ∧ p ∣ a
      --Goal : p ∣ prod (b :: L) → ∃ (a : Nat), a ∈ b :: L ∧ p ∣ a
    assume h2 : p ∣ prod (b :: L)
    rewrite [prod_cons] at h2
    have h3 : p ∣ b ∨ p ∣ prod L := Theorem_7_2_3 h1 h2
    by_cases on h3
    · -- Case 1. h3 : p ∣ b
      apply Exists.intro b
      show b ∈ b :: L ∧ p ∣ b from
        And.intro (List.mem_cons_self b L) h3
      done
    · -- Case 2. h3 : p ∣ prod L
      obtain (a : Nat) (h4 : a ∈ L ∧ p ∣ a) from ih h3
      apply Exists.intro a
      show a ∈ b :: L ∧ p ∣ a from
        And.intro (List.mem_cons_of_mem b h4.left) h4.right
      done
    done
  done

lemma prime_in_list {p : Nat} {l : List Nat}
    (h1 : prime p) (h2 : all_prime l) (h3 : p ∣ prod l) : p ∈ l := by
  obtain (a : Nat) (h4 : a ∈ l ∧ p ∣ a) from Theorem_7_2_4 h1 l h3
  define at h2
  have h5 : prime a := h2 a h4.left
  have h6 : p = 1 ∨ p = a := dvd_prime h5 h4.right
  disj_syll h6 (prime_not_one h1)
  rewrite [h6]
  show a ∈ l from h4.left
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
    linarith
    done
  · -- Case 2. h6 : q ∈ l
    have h8 : ∀ (m : Nat), m ∈ l → p ≤ m := h7.left
    show p ≤ q from h8 q h6
    done
  done

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

lemma prime_pos {p : Nat} (h : prime p) : p > 0 := by
  define at h
  linarith
  done

theorem Theorem_7_2_5 : ∀ (l1 l2 : List Nat),
    nondec_prime_list l1 → nondec_prime_list l2 →
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
    have h9 : p = q := by linarith
    rewrite [h9, prod_cons, prod_cons] at h3
      --h3 : q * prod L1 = q * prod L2
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

theorem fund_thm_arith (n : Nat) (h : n ≥ 1) :
    ∃! (l : List Nat), prime_factorization n l := by
  exists_unique
  · -- Existence
    show ∃ (l : List Nat), prime_factorization n l from
      exists_prime_factorization n h
    done
  · -- Uniqueness
    fix l1 : List Nat; fix l2 : List Nat
    assume h1 : prime_factorization n l1
    assume h2 : prime_factorization n l2
    define at h1; define at h2
    have h3 : prod l1 = n := h1.right
    rewrite [←h2.right] at h3
    show l1 = l2 from Theorem_7_2_5 l1 l2 h1.left h2.left h3
    done
  done

/- Section 7.3 -/
theorem congr_refl (m : Nat) : ∀ (a : Int), a ≡ a (MOD m) := by
  fix a : Int
  define                --Goal : ∃ (c : Int), a - a = ↑m * c
  apply Exists.intro 0
  norm_num
  done

theorem congr_symm {m : Nat} : ∀ {a b : Int},
    a ≡ b (MOD m) → b ≡ a (MOD m) := by
  fix a : Int; fix b : Int
  assume h1 : a ≡ b (MOD m)
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
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

/- Fundamental properties of congruence classes -/
lemma cc_eq_iff_val_eq {n : Nat} (X Y : ZMod (n + 1)) :
    X = Y ↔ X.val = Y.val := Fin.eq_iff_veq X Y

lemma val_nat_eq_mod (n k : Nat) :
    ([k]_(n + 1)).val = k % (n + 1) := by rfl

lemma val_zero (n : Nat) : ([0]_(n + 1)).val = 0 := by rfl

theorem cc_rep {m : Nat} (X : ZMod m) : ∃ (a : Int), X = [a]_m :=
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
    [a]_m + [b]_m = [a + b]_m := (Int.cast_add a b).symm

theorem mul_class (m : Nat) (a b : Int) :
    [a]_m * [b]_m = [a * b]_m := (Int.cast_mul a b).symm

lemma cc_eq_iff_sub_zero (m : Nat) (a b : Int) :
    [a]_m = [b]_m ↔ [a - b]_m = [0]_m := by
  apply Iff.intro
  · -- (→)
    assume h1 : [a]_m = [b]_m
    have h2 : a - b = a + (-b) := by ring
    have h3 : b + (-b) = 0 := by ring
    show [a - b]_m = [0]_m from
      calc [a - b]_m
        _ = [a + (-b)]_m := by rw [h2]
        _ = [a]_m + [-b]_m := by rw [add_class]
        _ = [b]_m + [-b]_m := by rw [h1]
        _ = [b + -b]_m := by rw [add_class]
        _ = [0]_m := by rw [h3]
    done
  · -- (←)
    assume h1 : [a - b]_m = [0]_m
    have h2 : b + (a - b) = a := by ring
    have h3 : b + 0 = b := by ring
    show [a]_m = [b]_m from
      calc [a]_m
        _ = [b + (a - b)]_m := by rw [h2]
        _ = [b]_m + [a - b]_m := by rw [add_class]
        _ = [b]_m + [0]_m := by rw [h1]
        _ = [b + 0]_m := by rw [add_class]
        _ = [b]_m := by rw [h3]
    done
  done

lemma cc_neg_zero_of_cc_zero (m : Nat) (a : Int) :
    [a]_m = [0]_m → [-a]_m = [0]_m := by
  assume h1 : [a]_m = [0]_m
  have h2 : 0 + (-a) = -a := by ring
  have h3 : a + (-a) = 0 := by ring
  show [-a]_m = [0]_m from
    calc [-a]_m
      _ = [0 + (-a)]_m := by rw [h2]
      _ = [0]_m + [-a]_m := by rw [add_class]
      _ = [a]_m + [-a]_m := by rw [h1]
      _ = [a + (-a)]_m := by rw [add_class]
      _ = [0]_m := by rw [h3]
  done

lemma cc_neg_zero_iff_cc_zero (m : Nat) (a : Int) :
    [-a]_m = [0]_m ↔ [a]_m = [0]_m := by
  apply Iff.intro _ (cc_neg_zero_of_cc_zero m a)
  assume h1 : [-a]_m = [0]_m
  have h2 : [-(-a)]_m = [0]_m := cc_neg_zero_of_cc_zero m (-a) h1
  have h3 : -(-a) = a := by ring
  rewrite [h3] at h2
  show [a]_m = [0]_m from h2
  done

lemma cc_mod_0 (a : Int) : [a]_0 = a := by rfl

lemma cc_nat_zero_iff_dvd (m k : Nat) : [k]_m = [0]_m ↔ m ∣ k :=
  match m with
    | 0 => by
      have h : (0 : Int) = (↑(0 : Nat) : Int) := by rfl
      rewrite [cc_mod_0, cc_mod_0, h, Nat.cast_inj]
      apply Iff.intro
      · -- (→)
        assume h1 : k = 0
        rewrite [h1]
        show 0 ∣ 0 from dvd_self 0
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

lemma cc_zero_iff_dvd (m : Nat) (a : Int) : [a]_m = [0]_m ↔ ↑m ∣ a := by
  obtain (k : Nat) (h1 : a = ↑k ∨ a = -↑k) from Int.eq_nat_or_neg a
  by_cases on h1
  · -- Case 1. h1: a = ↑k
    rewrite [h1, Int.coe_nat_dvd]
    show [↑k]_m = [0]_m ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  · -- Case 2. h1: a = -↑k
    rewrite [h1, cc_neg_zero_iff_cc_zero, Int.dvd_neg, Int.coe_nat_dvd]
    show [↑k]_m = [0]_m ↔ m ∣ k from cc_nat_zero_iff_dvd m k
    done
  done

theorem cc_eq_iff_congr (m : Nat) (a b : Int) :
    [a]_m = [b]_m ↔ a ≡ b (MOD m) :=
  calc [a]_m = [b]_m
    _ ↔ [a - b]_m = [0]_m := cc_eq_iff_sub_zero m a b
    _ ↔ ↑m ∣ (a - b) := cc_zero_iff_dvd m (a - b)
    _ ↔ a ≡ b (MOD m) := by rfl
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

lemma congr_mod_mod (m : Nat) (a : Int) : a ≡ a % m (MOD m) := by
  define
  have h1 : m * (a / m) + a % m = a := Int.ediv_add_emod a m
  apply Exists.intro (a / m)
  show a - a % m = m * (a / m) from
    calc a - (a % m)
      _ = m * (a / m) + a % m - a % m := by rw [h1]
      _ = m * (a / m) := by ring
  done

lemma mod_cmpl_res (m : Nat) [NeZero m] (a : Int) :
    0 ≤ a % m ∧ a % m < m ∧ a ≡ a % m (MOD m) :=
  And.intro (mod_nonneg m a) (And.intro (mod_lt m a) (congr_mod_mod m a))

theorem Theorem_7_3_1 (m : Nat) [NeZero m] (a : Int) :
    ∃! (r : Int), 0 ≤ r ∧ r < m ∧ a ≡ r (MOD m) := by
  exists_unique
  · -- Existence
    apply Exists.intro (a % m)
    show 0 ≤ a % m ∧ a % m < m ∧ a ≡ a % m (MOD m) from
      mod_cmpl_res m a
    done
  · -- Uniqueness
    fix r1 : Int; fix r2 : Int
    assume h1 : 0 ≤ r1 ∧ r1 < m ∧ a ≡ r1 (MOD m)
    assume h2 : 0 ≤ r2 ∧ r2 < m ∧ a ≡ r2 (MOD m)
    have h3 : r1 ≡ r2 (MOD m) :=
      congr_trans (congr_symm h1.right.right) h2.right.right
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

lemma cc_eq_mod (m : Nat) (a : Int) : [a]_m = [a % m]_m := 
  (cc_eq_iff_congr m a (a % m)).rtl (congr_mod_mod m a)

theorem Theorem_7_3_6_1 {m : Nat} (X Y : ZMod m) : X + Y = Y + X := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  obtain (b : Int) (h2 : Y = [b]_m) from cc_rep Y
  rewrite [h1, h2]
  have h3 : a + b = b + a := by ring
  show [a]_m + [b]_m = [b]_m + [a]_m from
    calc [a]_m + [b]_m
      _ = [a + b]_m := add_class m a b
      _ = [b + a]_m := by rw [h3]
      _ = [b]_m + [a]_m := (add_class m b a).symm
  done

theorem Theorem_7_3_6_7 {m : Nat} (X : ZMod m) : X * [1]_m = X := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  rewrite [h1]
  have h2 : a * 1 = a := by ring
  show [a]_m * [1]_m = [a]_m from
    calc [a]_m * [1]_m
      _ = [a * 1]_m := mul_class m a 1
      _ = [a]_m := by rw [h2]
  done

theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

lemma gcd_c2_inv {m a : Nat} (h1 : rel_prime m a) :
    [a]_m * [gcd_c2 m a]_m = [1]_m := by
  set s : Int := gcd_c1 m a
  have h2 : s * m + (gcd_c2 m a) * a = gcd m a := gcd_lin_comb a m
  define at h1
  rewrite [h1, Nat.cast_one] at h2  --h2 : s * ↑m + gcd_c2 m a * ↑a = 1
  rewrite [mul_class, cc_eq_iff_congr]
  define     --Goal : ∃ (c : Int), ↑a * gcd_c2 m a - 1 = ↑m * c
  apply Exists.intro (-s)
  show a * (gcd_c2 m a) - 1 = m * (-s) from
    calc a * (gcd_c2 m a) - 1
      _ = s * m + (gcd_c2 m a) * a + m * (-s) - 1 := by ring
      _ = 1 + m * (-s) - 1 := by rw [h2]
      _ = m * (-s) := by ring
  done

theorem Theorem_7_3_7 (m a : Nat) :
    invertible [a]_m ↔ rel_prime m a := by
  apply Iff.intro
  · -- (→)
    assume h1 : invertible [a]_m
    define at h1
    obtain (Y : ZMod m) (h2 : [a]_m * Y = [1]_m) from h1
    obtain (b : Int) (h3 : Y = [b]_m) from cc_rep Y
    rewrite [h3, mul_class, cc_eq_iff_congr] at h2
    define at h2
    obtain (c : Int) (h4 : a * b - 1 = m * c) from h2
    rewrite [Exercise_7_2_6]
      --Goal : ∃ (s t : Int), s * ↑m + t * ↑a = 1
    apply Exists.intro (-c)
    apply Exists.intro b
    show (-c) * m + b * a = 1 from
      calc (-c) * m + b * a
        _ = (-c) * m + (a * b - 1) + 1 := by ring
        _ = (-c) * m + m * c + 1 := by rw [h4]
        _ = 1 := by ring
    done
  · -- (←)
    assume h1 : rel_prime m a
    define
    show ∃ (Y : ZMod m), [a]_m * Y = [1]_m from
      Exists.intro [gcd_c2 m a]_m (gcd_c2_inv h1)
    done
  done

/- Section 7.4 -/
section Euler
open Euler

lemma num_rp_below_base {m : Nat} :
    num_rp_below m 0 = 0 := by rfl

lemma num_rp_below_step_rp {m j : Nat} (h : rel_prime m j) :
    num_rp_below m (j + 1) = (num_rp_below m j) + 1 := by
  have h1 : num_rp_below m (j + 1) =
    if gcd m j = 1 then (num_rp_below m j) + 1
    else num_rp_below m j := by rfl
  define at h     --h : gcd m j = 1
  rewrite [if_pos h] at h1
                  --h1 : num_rp_below m (j + 1) = num_rp_below m j + 1
  show num_rp_below m (j + 1) = num_rp_below m j + 1 from h1
  done

lemma num_rp_below_step_not_rp {m j : Nat} (h : ¬rel_prime m j) :
    num_rp_below m (j + 1) = num_rp_below m j := by
  have h1 : num_rp_below m (j +1) =
    if gcd m j = 1 then (num_rp_below m j) + 1
    else num_rp_below m j := by rfl
  define at h     --h : ¬gcd m j = 1
  rewrite [if_neg h] at h1
                  --h1 : num_rp_below m (j + 1) = num_rp_below m j
  show num_rp_below m (j + 1) = num_rp_below m j from h1
  done

lemma phi_def (m : Nat) : phi m = num_rp_below m m := by rfl

#eval phi 10    --Answer: 4

lemma prod_inv_iff_inv {m : Nat} {X : ZMod m}
    (h1 : invertible X) (Y : ZMod m) :
    invertible (X * Y) ↔ invertible Y := by
  apply Iff.intro
  · -- (→)
    assume h2 : invertible (X * Y)
    obtain (Z : ZMod m) (h3 : X * Y * Z = [1]_m) from h2
    apply Exists.intro (X * Z)
    rewrite [←h3]  --Goal : Y * (X * Z) = X * Y * Z
    ring     --Note that ring can do algebra in ZMod m
    done
  · -- (←)
    assume h2 : invertible Y
    obtain (Xi : ZMod m) (h3 : X * Xi = [1]_m) from h1
    obtain (Yi : ZMod m) (h4 : Y * Yi = [1]_m) from h2
    apply Exists.intro (Xi * Yi)
    show (X * Y) * (Xi * Yi) = [1]_m from
      calc X * Y * (Xi * Yi)
        _ = (X * Xi) * (Y * Yi) := by ring
        _ = [1]_m * [1]_m := by rw [h3, h4]
        _ = [1]_m := Theorem_7_3_6_7 [1]_m
    done
  done

lemma F_rp_def {m i : Nat} (h : rel_prime m i) :
    F m i = [i]_m := by
  have h1 : F m i = if gcd m i = 1 then [i]_m else [1]_m := by rfl
  define at h      --h : gcd m i = 1
  rewrite [if_pos h] at h1
  show F m i = [i]_m from h1
  done

lemma F_not_rp_def {m i : Nat} (h : ¬rel_prime m i) :
    F m i = [1]_m := by
  have h1 : F m i = if gcd m i = 1 then [i]_m else [1]_m := by rfl
  define at h
  rewrite [h1, if_neg h]
  rfl
  done

lemma prod_seq_base {m : Nat}
    (k : Nat) (f : Nat → ZMod m) : prod_seq 0 k f = [1]_m := by rfl

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

lemma G_def (m a i : Nat) : G m a i = (a * i) % m := by rfl

lemma cc_G (m a i : Nat) : [G m a i]_m = [a]_m * [i]_m :=
  calc [G m a i]_m
    _ = [(a * i) % m]_m := by rfl
    _ = [a * i]_m := (cc_eq_mod m (a * i)).symm
    _ = [a]_m * [i]_m := (mul_class m a i).symm

lemma G_rp_iff {m a : Nat} (h1 : rel_prime m a) (i : Nat) :
    rel_prime m (G m a i) ↔ rel_prime m i := by
  have h2 : invertible [a]_m := (Theorem_7_3_7 m a).rtl h1
  show rel_prime m (G m a i) ↔ rel_prime m i from
    calc rel_prime m (G m a i)
      _ ↔ invertible [G m a i]_m := (Theorem_7_3_7 m (G m a i)).symm
      _ ↔ invertible ([a]_m * [i]_m) := by rw [cc_G]
      _ ↔ invertible [i]_m := prod_inv_iff_inv h2 ([i]_m)
      _ ↔ rel_prime m i := Theorem_7_3_7 m i
  done

lemma FG_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : rel_prime m i) :
    F m (G m a i) = [a]_m * F m i := by
  have h3 : rel_prime m (G m a i) := (G_rp_iff h1 i).rtl h2
  show F m (G m a i) = [a]_m * F m i from
    calc F m (G m a i)
      _ = [G m a i]_m := F_rp_def h3
      _ = [a]_m * [i]_m := cc_G m a i
      _ = [a]_m * F m i := by rw [F_rp_def h2]
  done

lemma FG_not_rp {m a i : Nat} (h1 : rel_prime m a) (h2 : ¬rel_prime m i) :
    F m (G m a i) = [1]_m := by
  rewrite [←G_rp_iff h1 i] at h2
  show F m (G m a i) = [1]_m from F_not_rp_def h2
  done

lemma FG_prod {m a : Nat} (h1 : rel_prime m a) :
    ∀ (k : Nat), prod_seq k 0 ((F m) ∘ (G m a)) =
      [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) := by
  by_induc
  · -- Base Case
    show prod_seq 0 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m 0) * prod_seq 0 0 (F m) from
      calc prod_seq 0 0 ((F m) ∘ (G m a))
        _ = [1]_m := prod_seq_base _ _
        _ = [a]_m ^ 0 * [1]_m := by ring
        _ = [a]_m ^ (num_rp_below m 0) * prod_seq 0 0 (F m) := by
              rw [num_rp_below_base, prod_seq_base]
    done
  · -- Induction Step
    fix k : Nat
    assume ih : prod_seq k 0 ((F m) ∘ (G m a)) =
      [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m)
    by_cases h2 : rel_prime m k
    · -- Case 1. h2 : rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              ([a]_m * F m k) := by rw [FG_rp h1 h2]
          _ = [a]_m ^ ((num_rp_below m k) + 1) *
              ((prod_seq k 0 (F m)) * F m k) := by ring
          _ = [a]_m ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_rp h2, prod_seq_zero_step]
      done
    · -- Case 2. h2 : ¬rel_prime m k
      show prod_seq (k + 1) 0 ((F m) ∘ (G m a)) =
          [a]_m ^ (num_rp_below m (k + 1)) *
          prod_seq (k + 1) 0 (F m) from
        calc prod_seq (k + 1) 0 ((F m) ∘ (G m a))
          _ = prod_seq k 0 ((F m) ∘ (G m a)) *
              F m (G m a k) := prod_seq_zero_step _ _
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              F m (G m a k) := by rw [ih]
          _ = [a]_m ^ (num_rp_below m k) * prod_seq k 0 (F m) *
              ([1]_m) := by rw [FG_not_rp h1 h2]
          _ = [a]_m ^ (num_rp_below m k) *
              (prod_seq k 0 (F m) * ([1]_m)) := by ring
          _ = [a]_m ^ (num_rp_below m (k + 1)) *
              prod_seq (k + 1) 0 (F m) := by
                rw [num_rp_below_step_not_rp h2, prod_seq_zero_step,
                F_not_rp_def h2]
      done
    done
  done

lemma G_maps_below (m a : Nat) [NeZero m] : maps_below m (G m a) := by
  define             --Goal : ∀ (i : Nat), i < m → G m a i < m
  fix i : Nat
  assume h1 : i < m
  rewrite [G_def]    --Goal : a * i % m < m
  show a * i % m < m from mod_nonzero_lt (a * i) (NeZero.ne m)
  done

lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

lemma right_inv_onto_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g (g' i) = i) (h2 : maps_below n g') :
    onto_below n g := by
  define at h2; define
  fix k : Nat
  assume h3 : k < n
  apply Exists.intro (g' k)
  show g' k < n ∧ g (g' k) = k from And.intro (h2 k h3) (h1 k h3)
  done

lemma cc_mul_inv_mod_eq_one {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    [a]_m * [inv_mod m a]_m = [1]_m := by
  have h2 : 0 ≤ (gcd_c2 m a) % m := mod_nonneg m (gcd_c2 m a)
  show [a]_m * [inv_mod m a]_m = [1]_m from
    calc [a]_m * [inv_mod m a]_m
      _ = [a]_m * [Int.toNat ((gcd_c2 m a) % m)]_m := by rfl
      _ = [a]_m * [(gcd_c2 m a) % m]_m := by rw [Int.toNat_of_nonneg h2]
      _ = [a]_m * [gcd_c2 m a]_m := by rw [←cc_eq_mod]
      _ = [1]_m := gcd_c2_inv h1
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

theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

lemma mul_inv_mod_cancel {m a i : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : i < m) : a * (inv_mod m a) * i % m = i := by
  have h3 : [a]_m * [inv_mod m a]_m = [1]_m := cc_mul_inv_mod_eq_one h1
  rewrite [mul_class, cc_eq_iff_congr, ←Nat.cast_mul, ←Nat.cast_one, congr_iff_mod_eq_Nat] at h3
  show a * inv_mod m a * i % m = i from
    calc a * (inv_mod m a) * i % m
      _ = (a * inv_mod m a) % m * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = 1 % m * i % m := by rw [h3]
      _ = 1 * i % m := by rw [mod_mul_mod_eq_mul_mod]
      _ = i % m := by rw [one_mul]
      _ = i := Nat.mod_eq_of_lt h2
  done

lemma Ginv_def {m a i : Nat} : Ginv m a i = G m (inv_mod m a) i := by rfl

lemma Ginv_right_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    ∀ i < m, G m a (Ginv m a i) = i := by
  fix i : Nat
  assume h2 : i < m
  show G m a (Ginv m a i) = i from
    calc G m a (Ginv m a i)
      _ = a * ((inv_mod m a * i) % m) % m := by rfl
      _ = a * (inv_mod m a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc]
      _ = i := mul_inv_mod_cancel h1 h2
  done

lemma Ginv_left_inv {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    ∀ i < m, Ginv m a (G m a i) = i := by
  fix i : Nat
  assume h2 : i < m
  show Ginv m a (G m a i) = i from
    calc Ginv m a (G m a i)
      _ = inv_mod m a * ((a * i) % m) % m := by rfl
      _ = inv_mod m a * (a * i) % m := by rw [mul_mod_mod_eq_mul_mod]
      _ = a * inv_mod m a * i % m := by rw [←mul_assoc, mul_comm (inv_mod m a)]
      _ = i := mul_inv_mod_cancel h1 h2
  done

lemma Ginv_maps_below (m a : Nat) [NeZero m] :
    maps_below m (Ginv m a) := G_maps_below m (inv_mod m a)

lemma G_one_one_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    one_one_below m (G m a) :=
  left_inv_one_one_below (Ginv_left_inv h1)

lemma G_onto_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    onto_below m (G m a) :=
  right_inv_onto_below (Ginv_right_inv h1) (Ginv_maps_below m a)

lemma G_perm_below {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    perm_below m (G m a) := And.intro (G_maps_below m a)
  (And.intro (G_one_one_below h1) (G_onto_below h1))

--Permuting a product of congruence classes doesn't change product
lemma swap_fst (u v : Nat) : swap u v u = v := by
  define : swap u v u
    --Goal : (if u = u then v else if u = v then u else u) = v
  have h : u = u := by rfl
  rewrite [if_pos h]
  rfl
  done

lemma swap_snd (u v : Nat) : swap u v v = u := by
  define : swap u v v
  by_cases h1 : v = u
  · -- Case 1. h1 : v = u
    rewrite [if_pos h1]
    show v = u from h1
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
    show swap u v u = v from swap_fst u v
    done
  · -- Case 2. h1 : i ≠ u
    apply Or.inr
    by_cases h2 : i = v
    · -- Case 2.1. h2 : i = v
      apply Or.inl
      rewrite [h2]
      show swap u v v = u from swap_snd u v
      done
    · -- Case 2.2. h2 : i ≠ v
      apply Or.inr
      show swap u v i = i from swap_other h1 h2
      done
    done
  done

lemma swap_maps_below {u v n : Nat} (h1 : u < n) (h2 : v < n) : maps_below n (swap u v) := by
  define
  fix i : Nat
  assume h3 : i < n
  have h4 : swap u v i = v ∨ swap u v i = u ∨ swap u v i = i := swap_values u v i
  by_cases on h4
  · -- Case 1. h4 : swap u v i = v
    rewrite [h4]
    show v < n from h2
    done
  · -- Case 2.
    by_cases on h4
    · -- Case 2.1. h4 : swap u v i = u
      rewrite [h4]
      show u < n from h1
      done
    · -- Case 2.2. h4 : swap u v i = i
      rewrite [h4]
      show i < n from h3
      done
    done
  done

lemma swap_swap (u v n : Nat) : ∀ i < n, swap u v (swap u v i) = i := by
  fix i : Nat
  assume h : i < n
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

lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

lemma trivial_swap (u : Nat) : swap u u = id := by
  apply funext
  fix x : Nat
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
    assume h : (∀ (i : Nat), i < 0 → f (k + i) = g (k + i))
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : (∀ (i : Nat), i < n → f (k + i) = g (k + i)) → prod_seq n k f = prod_seq n k g
    assume h1 : ∀ (i : Nat), i < n + 1 → f (k + i) = g (k + i)
    have h2 : ∀ (i : Nat), i < n → f (k + i) = g (k + i) := by
      fix i : Nat
      assume h2 : i < n
      have h3 : i < n + 1 := by linarith
      show f (k + i) = g (k + i) from h1 i h3
      done
    have h3 : prod_seq n k f = prod_seq n k g := ih h2
    have h4 : n < n + 1 := Nat.lt_succ_self n
    rewrite [prod_seq_step, prod_seq_step, h3, h1 n h4]
    rfl
    done
  done

lemma swap_prod_eq_prod_below {m u n : Nat} (f : Nat → ZMod m)
    (h1 : u ≤ n) : prod_seq u 0 (f ∘ swap u n) = prod_seq u 0 f := by
  have h2 : ∀ (i : Nat), i < u → (f ∘ swap u n) (0 + i) = f (0 + i) := by
    fix i : Nat
    assume h2 : i < u
    have h3 : 0 + i ≠ u := by linarith
    have h4 : 0 + i ≠ n := by linarith
    rewrite [comp_def, swap_other h3 h4]
    rfl
    done
  show prod_seq u 0 (f ∘ swap u n) = prod_seq u 0 f from
    prod_eq_fun (f ∘ swap u n) f 0 u h2
  done

lemma swap_prod_eq_prod_between {m u j n : Nat} (f : Nat → ZMod m)
    (h1 : n = u + 1 + j) : prod_seq j (u + 1) (f ∘ swap u n) =
      prod_seq j (u + 1) f := by
  have h2 : ∀ i < j, (f ∘ swap u n) (u + 1 + i) = f (u + 1 + i) := by
    fix i : Nat
    assume h2 : i < j
    have h3 : u + 1 + i ≠ u := by linarith
    have h4 : u + 1 + i ≠ n := by linarith
    rewrite [comp_def, swap_other h3 h4]
    rfl
  show prod_seq j (u + 1) (f ∘ swap u n) = prod_seq j (u + 1) f from
    prod_eq_fun (f ∘ swap u n) f (u + 1) j h2
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
    fix j : Nat
    assume ih : prod_seq (n + j) 0 f = prod_seq n 0 f * prod_seq j n f
    rewrite [←add_assoc, prod_seq_zero_step, prod_seq_step, ih, mul_assoc]
    rfl
    done
  done

lemma break_prod_twice  {m u j n : Nat} (f : Nat → ZMod m)
    (h1 : n = u + 1 + j) : prod_seq (n + 1) 0 f =
      prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n := by
  have h2 : prod_seq (n + 1) 0 f = prod_seq n 0 f * prod_seq 1 n f :=
    break_prod n f 1
  rewrite [prod_one] at h2
  have h3 : prod_seq (u + 1 + j) 0 f = prod_seq (u + 1) 0 f * prod_seq j (u + 1) f :=
    break_prod (u + 1) f j
  rewrite [←h1] at h3
  have h4 : prod_seq (u + 1) 0 f = prod_seq u 0 f * prod_seq 1 u f :=
    break_prod u f 1
  rewrite [prod_one] at h4
  rewrite [h3, h4] at h2
  show prod_seq (n + 1) 0 f = prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n from h2
  done

lemma swap_prod_eq_prod {m u n : Nat} (f : Nat → ZMod m) (h1 : u ≤ n) :
    prod_seq (n + 1) 0 (f ∘ swap u n) = prod_seq (n + 1) 0 f := by
  by_cases h2 : u = n
  · -- Case 1. h2 : u = n
    rewrite [h2, trivial_swap n]
      --Goal : prod_seq (n + 1) 0 (f ∘ id) = prod_seq (n + 1) 0 f
    rfl
    done
  · -- Case 2. h2 : ¬u = n
    have h3 : u + 1 ≤ n := Nat.lt_of_le_of_ne h1 h2
    obtain (j : Nat) (h4 : n = u + 1 + j) from Nat.exists_eq_add_of_le h3
    have break_f : prod_seq (n + 1) 0 f =
      prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n :=
      break_prod_twice f h4
    have break_fs : prod_seq (n + 1) 0 (f ∘ swap u n) =
      prod_seq u 0 (f ∘ swap u n) * (f ∘ swap u n) u *
      prod_seq j (u + 1) (f ∘ swap u n) * (f ∘ swap u n) n :=
      break_prod_twice (f ∘ swap u n) h4
    have f_eq_fs_below : prod_seq u 0 (f ∘ swap u n) =
      prod_seq u 0 f := swap_prod_eq_prod_below f h1
    have f_eq_fs_btwn : prod_seq j (u + 1) (f ∘ swap u n) =
      prod_seq j (u + 1) f := swap_prod_eq_prod_between f h4
    show prod_seq (n + 1) 0 (f ∘ swap u n) = prod_seq (n + 1) 0 f from
      calc prod_seq (n + 1) 0 (f ∘ swap u n)
        _ = prod_seq u 0 (f ∘ swap u n) * (f ∘ swap u n) u *
            prod_seq j (u + 1) (f ∘ swap u n) * (f ∘ swap u n) n :=
              break_fs
        _ = prod_seq u 0 f * (f ∘ swap u n) u *
            prod_seq j (u + 1) f * (f ∘ swap u n) n := by
              rw [f_eq_fs_below, f_eq_fs_btwn]
        _ = prod_seq u 0 f * f (swap u n u) *
            prod_seq j (u + 1) f * f (swap u n n) := by rfl
        _ = prod_seq u 0 f * f n * prod_seq j (u + 1) f * f u := by
              rw [swap_fst, swap_snd]
        _ = prod_seq u 0 f * f u * prod_seq j (u + 1) f * f n := by ring
        _ = prod_seq (n + 1) 0 f := break_f.symm
    done
  done

lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

lemma perm_prod {m : Nat} (f : Nat → ZMod m) :
    ∀ (n : Nat), ∀ (g : Nat → Nat), perm_below n g →
      prod_seq n 0 f = prod_seq n 0 (f ∘ g) := by
  by_induc
  · -- Base Case
    fix g : Nat → Nat
    assume h1 : perm_below 0 g
    rewrite [prod_seq_base, prod_seq_base]
    rfl
    done
  · -- Induction Step
    fix n : Nat
    assume ih : ∀ (g : Nat → Nat), perm_below n g →
      prod_seq n 0 f = prod_seq n 0 (f ∘ g)
    fix g : Nat → Nat
    assume g_pb : perm_below (n + 1) g
    define at g_pb
    have g_ob : onto_below (n + 1) g := g_pb.right.right
    define at g_ob
    have h1 : n < n + 1 := by linarith
    obtain (u : Nat) (h2 : u < n + 1 ∧ g u = n) from g_ob n h1
    have s_pb : perm_below (n + 1) (swap u n) :=
      swap_perm_below h2.left h1
    have gs_pb_n1 : perm_below (n + 1) (g ∘ swap u n) :=
      comp_perm_below g_pb s_pb
    have gs_fix_n : (g ∘ swap u n) n = n :=
      calc (g ∘ swap u n) n
        _ = g (swap u n n) := by rfl
        _ = g u := by rw [swap_snd]
        _ = n := h2.right
    have gs_pb_n : perm_below n (g ∘ swap u n) :=
      perm_below_fixed gs_pb_n1 gs_fix_n
    have gs_prod : prod_seq n 0 f = prod_seq n 0 (f ∘ (g ∘ swap u n)) :=
      ih (g ∘ swap u n) gs_pb_n
    have h3 : u ≤ n := by linarith
    show prod_seq (n + 1) 0 f = prod_seq (n + 1) 0 (f ∘ g) from
      calc prod_seq (n + 1) 0 f
        _ = prod_seq n 0 f * f n := prod_seq_zero_step n f
        _ = prod_seq n 0 (f ∘ (g ∘ swap u n)) *
            f ((g ∘ swap u n) n) := by rw [gs_prod, gs_fix_n]
        _ = prod_seq n 0 (f ∘ g ∘ swap u n) *
            (f ∘ g ∘ swap u n) n := by rfl
        _ = prod_seq (n + 1) 0 (f ∘ g ∘ swap u n) :=
              (prod_seq_zero_step n (f ∘ g ∘ swap u n)).symm
        _ = prod_seq (n + 1) 0 ((f ∘ g) ∘ swap u n) := by rfl
        _ = prod_seq (n + 1) 0 (f ∘ g) := swap_prod_eq_prod (f ∘ g) h3
    done
  done

lemma F_invertible (m i : Nat) : invertible (F m i) := by
  by_cases h : rel_prime m i
  · -- Case 1. h : rel_prime m i
    rewrite [F_rp_def h]
    show invertible [i]_m from (Theorem_7_3_7 m i).rtl h
    done
  · -- Case 2. h : ¬rel_prime m i
    rewrite [F_not_rp_def h]
    apply Exists.intro [1]_m
    show [1]_m * [1]_m = [1]_m from Theorem_7_3_6_7 [1]_m
    done
  done

lemma Fprod_invertible (m : Nat) :
    ∀ (k : Nat), invertible (prod_seq k 0 (F m)) := by
  by_induc
  · -- Base Case
    apply Exists.intro [1]_m
    show prod_seq 0 0 (F m) * [1]_m = [1]_m from
      calc prod_seq 0 0 (F m) * [1]_m
        _ = [1]_m * [1]_m := by rw [prod_seq_base]
        _ = [1]_m := Theorem_7_3_6_7 ([1]_m)
    done
  · -- Induction Step
    fix k : Nat
    assume ih : invertible (prod_seq k 0 (F m))
    rewrite [prod_seq_zero_step]
    show invertible (prod_seq k 0 (F m) * (F m k)) from
      (prod_inv_iff_inv ih (F m k)).rtl (F_invertible m k)
    done
  done

theorem Theorem_7_4_2 {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    [a]_m ^ (phi m) = [1]_m := by
  have h2 : invertible (prod_seq m 0 (F m)) := Fprod_invertible m m
  obtain (Y : ZMod m) (h3 : prod_seq m 0 (F m) * Y = [1]_m) from h2
  show [a]_m ^ (phi m) = [1]_m from
    calc [a]_m ^ (phi m)
      _ = [a]_m ^ (phi m) * [1]_m := (Theorem_7_3_6_7 _).symm
      _ = [a]_m ^ (phi m) * (prod_seq m 0 (F m) * Y) := by rw [h3]
      _ = ([a]_m ^ (phi m) * prod_seq m 0 (F m)) * Y := by ring
      _ = prod_seq m 0 (F m ∘ G m a) * Y := by rw [FG_prod h1 m, phi_def]
      _ = prod_seq m 0 (F m) * Y := by
            rw [perm_prod (F m) m (G m a) (G_perm_below h1)]
      _ = [1]_m := by rw [h3]
  done

lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

lemma Exercise_7_4_5_Nat (m a n : Nat) :
    [a]_m ^ n = [a ^ n]_m := by
  rewrite [Exercise_7_4_5_Int, Nat.cast_pow]
  rfl
  done

theorem Euler's_theorem {m a : Nat} [NeZero m]
    (h1 : rel_prime m a) : a ^ (phi m) ≡ 1 (MOD m) := by
  have h2 : [a]_m ^ (phi m) = [1]_m := Theorem_7_4_2 h1
  rewrite [Exercise_7_4_5_Nat m a (phi m)] at h2
    --h2 : [↑(a ^ phi m)]_m = [1]_m
  show a ^ (phi m) ≡ 1 (MOD m) from (cc_eq_iff_congr _ _ _).ltr h2
  done

#eval gcd 10 7     --Answer: 1.  So 10 and 7 are relatively prime

#eval 7 ^ phi 10   --Answer: 2401, which is congruent to 1 mod 10.

end Euler

/- Section 7.5 -/
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ (k : Nat), k < p → num_rp_below p (k + 1) = k := sorry

lemma phi_prime {p : Nat} (h1 : prime p) : phi p = p - 1 := by
  have h2 : 1 ≤ p := prime_pos h1
  have h3 : p - 1 + 1 = p := Nat.sub_add_cancel h2
  have h4 : p - 1 < p := by linarith
  have h5 : num_rp_below p (p - 1 + 1) = p - 1 :=
    num_rp_prime h1 (p - 1) h4
  rewrite [h3] at h5
  show phi p = p - 1 from h5
  done

theorem Theorem_7_2_2_Int {a c : Nat} {b : Int}
    (h1 : ↑c ∣ ↑a * b) (h2 : rel_prime a c) : ↑c ∣ b := by
  rewrite [Int.coe_nat_dvd_left, Int.natAbs_mul,
    Int.natAbs_ofNat] at h1        --h1 : c ∣ a * Int.natAbs b
  rewrite [Int.coe_nat_dvd_left]   --Goal : c ∣ Int.natAbs b
  show c ∣ Int.natAbs b from Theorem_7_2_2 h1 h2
  done

lemma Lemma_7_4_5 {m n : Nat} (a b : Int) (h1 : rel_prime m n) :
    a ≡ b (MOD m * n) ↔ a ≡ b (MOD m) ∧ a ≡ b (MOD n) := by
  apply Iff.intro
  · -- (→)
    assume h2 : a ≡ b (MOD m * n)
    obtain (j : Int) (h3 : a - b = (m * n) * j) from h2
    apply And.intro
    · -- Proof of a ≡ b (MOD m)
      apply Exists.intro (n * j)
      show a - b = m * (n * j) from
        calc a - b
          _ = m * n * j := h3
          _ = m * (n * j) := by ring
      done
    · -- Proof of a ≡ b (MOD n)
      apply Exists.intro (m * j)
      show a - b = n * (m * j) from
        calc a - b
          _ = m * n * j := h3
          _ = n * (m * j) := by ring
      done
    done
  · -- (←)
    assume h2 : a ≡ b (MOD m) ∧ a ≡ b (MOD n)
    obtain (j : Int) (h3 : a - b = m * j) from h2.left
    have h4 : (↑n : Int) ∣ a - b := h2.right
    rewrite [h3] at h4      --h4 : ↑n ∣ ↑m * j
    have h5 : ↑n ∣ j := Theorem_7_2_2_Int h4 h1
    obtain (k : Int) (h6 : j = n * k) from h5
    apply Exists.intro k    --Goal : a - b = ↑(m * n) * k
    show a - b = (m * n) * k from
      calc a - b
        _ = m * j := h3
        _ = m * (n * k) := by rw [h6]
        _ = (m * n) * k := by ring
    done
  done

--From exercises of Section 7.2
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

lemma prime_NeZero {p : Nat} (h : prime p) : NeZero p := by
  rewrite [neZero_iff]     --Goal : p ≠ 0
  define at h
  linarith
  done

lemma Lemma_7_5_1 {p e d m c s : Nat} {t : Int}
    (h1 : prime p) (h2 : e * d = (p - 1) * s + 1)
    (h3 : ↑(m ^ e) - ↑c = ↑p * t) :
    c ^ d ≡ m (MOD p) := by
  have h4 : m ^ e ≡ c (MOD p) := Exists.intro t h3
  have h5 : [m ^ e]_p = [c]_p := (cc_eq_iff_congr _ _ _).rtl h4
  rewrite [←Exercise_7_4_5_Nat] at h5  --h5 : [m]_p ^ e = [c]_p
  by_cases h6 : p ∣ m
  · -- Case 1. h6 : p ∣ m
    have h7 : m ≡ 0 (MOD p) := by
      obtain (j : Nat) (h8 : m = p * j) from h6
      apply Exists.intro (↑j : Int)   --Goal : ↑m - 0 = ↑p * ↑j
      rewrite [h8, Nat.cast_mul]
      ring
      done
    have h8 : [m]_p = [0]_p := (cc_eq_iff_congr _ _ _).rtl h7
    have h9 : 0 < (e * d) := by
      rewrite [h2]
      have h10 : 0 ≤ (p - 1) * s := Nat.zero_le _
      linarith
      done
    have h10 : (0 : Int) ^ (e * d) = 0 := zero_pow h9
    have h11 : [c ^ d]_p = [m]_p :=
      calc [c ^ d]_p
        _ = [c]_p ^ d := by rw [Exercise_7_4_5_Nat]
        _ = ([m]_p ^ e) ^ d := by rw [h5]
        _ = [m]_p ^ (e * d) := by ring
        _ = [0]_p ^ (e * d) := by rw [h8]
        _ = [0 ^ (e * d)]_p := Exercise_7_4_5_Int _ _ _
        _ = [0]_p := by rw [h10]
        _ = [m]_p := by rw [h8]
    show c ^ d ≡ m (MOD p)  from (cc_eq_iff_congr _ _ _).ltr h11
    done
  · -- Case 2. h6 : ¬p ∣ m
    have h7 : rel_prime m p := rel_prime_of_prime_not_dvd h1 h6
    have h8 : rel_prime p m := rel_prime_symm h7
    have h9 : NeZero p := prime_NeZero h1
    have h10 : (1 : Int) ^ s = 1 := by ring
    have h11 : [c ^ d]_p = [m]_p :=
      calc [c ^ d]_p
        _ = [c]_p ^ d := by rw [Exercise_7_4_5_Nat]
        _ = ([m]_p ^ e) ^ d := by rw [h5]
        _ = [m]_p ^ (e * d) := by ring
        _ = [m]_p ^ ((p - 1) * s + 1) := by rw [h2]
        _ = ([m]_p ^ (p - 1)) ^ s * [m]_p := by ring
        _ = ([m]_p ^ (phi p)) ^ s * [m]_p := by rw [phi_prime h1]
        _ = [1]_p ^ s * [m]_p := by rw [Theorem_7_4_2 h8]
        _ = [1 ^ s]_p * [m]_p := by rw [Exercise_7_4_5_Int]
        _ = [1]_p * [m]_p := by rw [h10]
        _ = [m]_p * [1]_p := by ring
        _ = [m]_p := Theorem_7_3_6_7 _
    show c ^ d ≡ m (MOD p)  from (cc_eq_iff_congr _ _ _).ltr h11
    done
  done

theorem Theorem_7_5_1 (p q n e d k m c : Nat)
    (p_prime : prime p) (q_prime : prime q) (p_ne_q : p ≠ q)
    (n_pq : n = p * q) (ed_congr_1 : e * d = k * (p - 1) * (q - 1) + 1)
    (h1 : [m]_n ^ e = [c]_n) : [c]_n ^ d = [m]_n := by
  rewrite [Exercise_7_4_5_Nat, cc_eq_iff_congr] at h1
    --h1 : m ^ e ≡ c (MOD n)
  rewrite [Exercise_7_4_5_Nat, cc_eq_iff_congr]
    --Goal : c ^ d ≡ m (MOD n)
  obtain (j : Int) (h2 : ↑(m ^ e) - ↑c = ↑n * j) from h1
  rewrite [n_pq, Nat.cast_mul] at h2
    --h2 : ↑(m ^ e) - ↑c = ↑p * ↑q * j
  have h3 : e * d = (p - 1) * (k * (q - 1)) + 1 := by
    rewrite [ed_congr_1]
    ring
    done
  have h4 : ↑(m ^ e) - ↑c = ↑p * (↑q * j) := by
    rewrite [h2]
    ring
    done
  have congr_p : c ^ d ≡ m (MOD p) := Lemma_7_5_1 p_prime h3 h4
  have h5 : e * d = (q - 1) * (k * (p - 1)) + 1 := by
    rewrite [ed_congr_1]
    ring
    done
  have h6 : ↑(m ^ e) - ↑c = ↑q * (↑p * j) := by
    rewrite [h2]
    ring
    done
  have congr_q : c ^ d ≡ m (MOD q) := Lemma_7_5_1 q_prime h5 h6
  have h7 : ¬q ∣ p := by
    by_contra h8
    have h9 : q = 1 ∨ q = p := dvd_prime p_prime h8
    disj_syll h9 (prime_not_one q_prime)
    show False from p_ne_q h9.symm
    done
  have h8 : rel_prime p q := rel_prime_of_prime_not_dvd q_prime h7
  rewrite [n_pq, Lemma_7_4_5 _ _ h8]
  show c ^ d ≡ m (MOD p) ∧ c ^ d ≡ m (MOD q) from
    And.intro congr_p congr_q
  done