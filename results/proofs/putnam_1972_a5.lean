import Mathlib
open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

theorem exists_minimal_prime_factor (n : ℕ) (hn : 1 < n)
    (hdiv : (n : ℤ) ∣ (2^n - 1 : ℤ)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ (∀ m, m ∣ n → 1 < m → p ≤ m) ∧
      (p : ℤ) ∣ (2^n - 1 : ℤ) ∧ p ≠ 2 := by
  classical
  let P : ℕ → Prop := fun d => Nat.Prime d ∧ d ∣ n
  have hP : ∃ d, P d := by
    obtain ⟨pp, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨pp, hpp, hpdvd⟩
  let p := Nat.find hP
  have hp : P p := Nat.find_spec hP
  obtain ⟨hp_prime, hp_dvd⟩ := hp
  have hPmin : ∀ q, Nat.Prime q → q ∣ n → p ≤ q := by
    intro q hq hqdvd
    refine Nat.le_of_not_lt ?_
    intro hlt
    exact Nat.find_min hP hlt ⟨hq, hqdvd⟩
  have hp_min : ∀ m, m ∣ n → 1 < m → p ≤ m := by
    intro m hmn h1m
    obtain ⟨q, hq_prime, hq_dvd_m⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hq_dvd_n : q ∣ n := hq_dvd_m.trans hmn
    have hq_le_m : q ≤ m := Nat.le_of_dvd (by omega) hq_dvd_m
    exact Nat.le_trans (hPmin q hq_prime hq_dvd_n) hq_le_m
  have hp_int_dvd : (p : ℤ) ∣ (2^n - 1 : ℤ) := by
    have hpn : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hp_dvd
    exact hpn.trans hdiv
  have hp_ne2 : p ≠ 2 := by
    intro h2
    have h2_div : (2 : ℤ) ∣ ((2 : ℤ)^n - 1) := by
      simpa [h2] using hp_int_dvd
    have hpow : (2 : ℤ) ∣ (2 : ℤ)^n := by
      first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
    have h1 : (2 : ℤ) ∣ ((2 : ℤ)^n - ((2 : ℤ)^n - 1)) := hpow.sub h2_div
    have h1eq : (2 : ℤ)^n - ((2 : ℤ)^n - 1) = (1 : ℤ) := by ring
    rw [h1eq] at h1
    rcases h1 with ⟨k, hk⟩
    omega
  exact ⟨p, hp_prime, hp_dvd, hp_min, hp_int_dvd, hp_ne2⟩

theorem gcd_one_of_min_prime_factor (n p : ℕ)
    (hp : Nat.Prime p) (hpd : p ∣ n)
    (hmin : ∀ m, m ∣ n → 1 < m → p ≤ m) :
    Nat.gcd n (p - 1) = 1 := by
  by_contra hne
  have hpb : 0 < p - 1 := by
    have := Nat.Prime.one_lt hp
    omega
  have h0 : 0 < Nat.gcd n (p - 1) := by
    rcases Nat.eq_zero_or_pos (Nat.gcd n (p - 1)) with hz | hpos
    · obtain ⟨c, hc⟩ := Nat.gcd_dvd_right n (p - 1)
      rw [hz] at hc
      simp at hc
      omega
    · exact hpos
  have hd : 1 < Nat.gcd n (p - 1) := by omega
  obtain ⟨q, hq, hqd⟩ : ∃ q, Nat.Prime q ∧ q ∣ Nat.gcd n (p - 1) :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt hd)
  have hqn : q ∣ n := Nat.dvd_trans hqd (Nat.gcd_dvd_left n (p - 1))
  have hqp : q ∣ p - 1 := Nat.dvd_trans hqd (Nat.gcd_dvd_right n (p - 1))
  have hqle : q ≤ p - 1 := Nat.le_of_dvd hpb hqp
  have hq_lt_p : q < p := by
    have := Nat.Prime.one_lt hp
    omega
  have hpq : p ≤ q := hmin q hqn (Nat.Prime.one_lt hq)
  omega

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set

/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

theorem order_dvd_gcd_two (n p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hdiv : (p : ℤ) ∣ (2^n - 1 : ℤ)) :
    orderOf (2 : ZMod p) ∣ Nat.gcd n (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := by
      exact (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (Nat.le_antisymm hle hge)
  have hmod : ((2^n - 1 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2^n - 1) p).mpr hdiv
  have hcast : ((2^n - 1 : ℤ) : ZMod p) = (2 : ZMod p)^n - 1 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hpow : (2 : ZMod p)^n = 1 := by
    have h0 : (2 : ZMod p)^n - 1 = 0 := by
      rw [← hcast, hmod]
    exact sub_eq_zero.mp h0
  have hfpow : (2 : ZMod p)^(p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h2ne0
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow)
    (orderOf_dvd_of_pow_eq_one hfpow)

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

open EuclideanGeometry Filter Topology Set


/-
Informal proof sketch:
Assume n > 1 and n ∣ 2^n - 1. Let p be the smallest prime divisor of n.
Since n ∣ 2^n - 1, we also have p ∣ 2^n - 1. Also p ≠ 2, because 2^n - 1 is odd.
By minimality of p, gcd(n, p - 1) = 1: any common divisor d > 1 would have a prime
factor q ∣ n with q < p, contradicting minimality.
Working modulo p, since p is odd and p ∣ 2^n - 1, the element 2 ∈ ZMod p has finite
order dividing both n (because 2^n ≡ 1) and p - 1 (by Fermat's little theorem).
Hence its order divides gcd(n, p - 1) = 1, so the order is 1. But order 1 would mean
2 ≡ 1 (mod p), i.e. p ∣ 1, impossible for a prime p. Contradiction.
-/

theorem not_order_one_two (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 1 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    simpa using orderOf_eq_one_iff.mp h
  have h0 : (1 : ZMod p) = 0 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hdiv : p ∣ 1 := by
    haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
    rw [← ZMod.natCast_eq_zero_iff]
    exact_mod_cast h0
  exact hp.ne_one (Nat.eq_one_of_dvd_one hdiv)

/--
Show that if $n$ is an integer greater than $1$, then $n$ does not divide $2^n - 1$.
-/
theorem putnam_1972_a5
(n : ℕ)
(hn : n > 1)
: ¬((n : ℤ) ∣ 2^n - 1) := by
  intro h
  have h' : (n : ℤ) ∣ (2^n - 1 : ℤ) := h
  obtain ⟨p, hp, hpd, hmin, hpdiv, hp2⟩ :=
    exists_minimal_prime_factor n (by omega : 1 < n) h'
  have hgcd : Nat.gcd n (p - 1) = 1 :=
    gcd_one_of_min_prime_factor n p hp hpd hmin
  have hord : orderOf (2 : ZMod p) ∣ Nat.gcd n (p - 1) :=
    order_dvd_gcd_two n p hp hp2 hpdiv
  have hord1 : orderOf (2 : ZMod p) = 1 := by
    rw [hgcd] at hord
    exact Nat.dvd_one.mp hord
  exact not_order_one_two p hp hp2 hord1

#print axioms putnam_1972_a5
