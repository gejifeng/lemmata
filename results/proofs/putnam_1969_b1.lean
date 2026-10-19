import Mathlib
open Matrix Filter Topology Set Nat


open Nat

open BigOperators

theorem residue_from_24 (n : ℕ) (hnpos : n > 0) (h : 24 ∣ n + 1) :
    n % 3 = 2 ∧ n % 8 = 7 := by
  intros
  first
  | omega
  | linarith
  | positivity
  | norm_num
  | (simp_all; done)
  | ring

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

theorem sum_finset_pairing (s : Finset ℕ) (m : ℕ) (hm : 0 < m) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, f x ∈ s)
    (hinv : ∀ x ∈ s, f (f x) = x)
    (hfix : ∀ x ∈ s, f x ≠ x)
    (hsum : ∀ x ∈ s, m ∣ x + f x) :
    m ∣ ∑ x ∈ s, x := by
  let t := s.filter (fun x => x < f x)
  have h_inj : Set.InjOn f (t : Set ℕ) := by
    intro x hx y hy hxy
    have hx_s : x ∈ s := (Finset.mem_filter.mp hx).1
    have hy_s : y ∈ s := (Finset.mem_filter.mp hy).1
    rw [← hinv x hx_s, ← hinv y hy_s, hxy]
  have hsplit : s = t ∪ t.image f := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hdisj : Disjoint t (t.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hmem
    obtain ⟨y, hy, hyf⟩ := Finset.mem_image.mp hmem
    have hy_s : y ∈ s := (Finset.mem_filter.mp hy).1
    have hfx_eq_y : f x = y := by
      rw [← hyf]
      exact hinv y hy_s
    have hx_lt_y : x < y := by
      have hx_lt : x < f x := (Finset.mem_filter.mp hx).2
      rwa [hfx_eq_y] at hx_lt
    have hy_lt_x : y < x := by
      have hy_lt : y < f y := (Finset.mem_filter.mp hy).2
      rwa [hyf] at hy_lt
    exact Nat.lt_asymm hy_lt_x hx_lt_y
  have hsum_image : ∑ x ∈ t.image f, x = ∑ x ∈ t, f x := by
    simpa using Finset.sum_image h_inj
  rw [hsplit, Finset.sum_union hdisj, hsum_image, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum (fun x hx => hsum x ((Finset.mem_filter.mp hx).1))

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

lemma nat_mod3_lt_cases (r : ℕ) (hr : r < 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  cases r with
  | zero => left; rfl
  | succ r1 =>
    cases r1 with
    | zero => right; left; rfl
    | succ r2 =>
      cases r2 with
      | zero => right; right; rfl
      | succ r3 => exact absurd hr (by omega)

theorem divisors_pair_data_mod_3 (n : ℕ) (hnpos : 0 < n) (h : n % 3 = 2) (d : ℕ)
    (hd : d ∈ Nat.divisors n) :
    (n / d) ∈ Nat.divisors n ∧ n / (n / d) = d ∧ n / d ≠ d ∧ 3 ∣ d + n / d := by
  obtain ⟨hdvd, hn0⟩ := (Nat.mem_divisors).mp hd
  have hn0' : n ≠ 0 := by omega
  let e := n / d
  have h_eq_mul : e * d = n := Nat.div_mul_cancel hdvd
  have h_eq : n = d * e := by
    rw [Nat.mul_comm, h_eq_mul]
  have hprod : (d * e) % 3 = 2 := by
    rw [← h_eq, h]
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with hz | hp
    · rw [hz] at h_eq
      omega
    · exact hp
  have hd_not3 : ¬ 3 ∣ d := by
    intro hd3
    have hprod0 : (d * e) % 3 = 0 := Nat.mod_eq_zero_of_dvd (hd3.mul_right e)
    omega
  have he_not3 : ¬ 3 ∣ e := by
    intro he3
    have hprod0 : (d * e) % 3 = 0 := Nat.mod_eq_zero_of_dvd (he3.mul_left d)
    omega
  have hd_cases : d % 3 = 1 ∨ d % 3 = 2 := by
    rcases nat_mod3_lt_cases (d % 3) (Nat.mod_lt d (by norm_num)) with h0 | h1 | h2
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) hd_not3
    · left; exact h1
    · right; exact h2
  have he_cases : e % 3 = 1 ∨ e % 3 = 2 := by
    rcases nat_mod3_lt_cases (e % 3) (Nat.mod_lt e (by norm_num)) with h0 | h1 | h2
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) he_not3
    · left; exact h1
    · right; exact h2
  have hprod3 : ((d % 3) * (e % 3)) % 3 = 2 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hsum3 : (d + e) % 3 = 0 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hdiv : 3 ∣ d + e := Nat.dvd_iff_mod_eq_zero.mpr hsum3
  have hne : e ≠ d := by
    intro hde
    have hprod3' : ((d % 3) * (d % 3)) % 3 = 2 := by
      have := hprod3
      rw [hde] at this
      exact this
    rcases hd_cases with hdr | hdr
    · rw [hdr] at hprod3'
      exact absurd hprod3' (by norm_num)
    · rw [hdr] at hprod3'
      exact absurd hprod3' (by norm_num)
  have he_div : e ∈ Nat.divisors n := by
    refine (Nat.mem_divisors).mpr ⟨?_, ?_⟩
    · exact ⟨d, h_eq_mul.symm⟩
    · exact hn0'
  have h_div_e : n / e = d := by
    rw [h_eq]
    exact Nat.mul_div_cancel d (by omega)
  exact ⟨he_div, h_div_e, hne, hdiv⟩

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

open Matrix Filter Topology Set Nat

open Nat

open BigOperators

private lemma odd_pair_mod8 {a b : ℕ} (ha : a < 8) (hb : b < 8)
    (haodd : a % 2 = 1) (hbodd : b % 2 = 1) (hab : a * b % 8 = 7) :
    (a + b) % 8 = 0 := by
  interval_cases a <;> interval_cases b <;> simp_all

theorem divisors_pair_data_mod_8 (n : ℕ) (hnpos : 0 < n) (h : n % 8 = 7) (d : ℕ)
    (hd : d ∈ Nat.divisors n) :
    (n / d) ∈ Nat.divisors n ∧ n / (n / d) = d ∧ n / d ≠ d ∧ 8 ∣ d + n / d := by
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, hdne⟩ := hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero (fun hz => hdne (by
    have : d ∣ n := hdvd
    simp [hz] at this
    omega))
  set q := n / d with hqdef
  have hprod : q * d = n := by
    rw [hqdef]
    exact Nat.div_mul_cancel hdvd
  have hqvd : q ∣ n := ⟨d, hprod.symm⟩
  have hqne : q ≠ 0 := by
    intro hq
    rw [hq] at hprod
    simp at hprod
    omega
  have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
  have hnodd : n % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8), h]
  have hdodd : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
    · have h2n : 2 ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero h0) hdvd
      have := Nat.mod_eq_zero_of_dvd h2n
      omega
    · exact h1
  have hqodd : q % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
    · have h2n : 2 ∣ n := dvd_trans (Nat.dvd_of_mod_eq_zero h0) hqvd
      have := Nat.mod_eq_zero_of_dvd h2n
      omega
    · exact h1
  set a := d % 8 with ha_def
  set b := q % 8 with hb_def
  have ha : a < 8 := Nat.mod_lt d (by decide)
  have hb : b < 8 := Nat.mod_lt q (by decide)
  have haodd : a % 2 = 1 := by
    rw [ha_def, Nat.mod_mod_of_dvd d (by decide : 2 ∣ 8)]
    exact hdodd
  have hbodd : b % 2 = 1 := by
    rw [hb_def, Nat.mod_mod_of_dvd q (by decide : 2 ∣ 8)]
    exact hqodd
  have hab : a * b % 8 = 7 := by
    rw [ha_def, hb_def]
    calc (d % 8) * (q % 8) % 8 = (d * q) % 8 := (Nat.mul_mod d q 8).symm
      _ = (q * d) % 8 := by rw [Nat.mul_comm]
      _ = n % 8 := by rw [hprod]
      _ = 7 := h
  have hsum_mod : (a + b) % 8 = 0 := odd_pair_mod8 ha hb haodd hbodd hab
  have hdiv8 : 8 ∣ d + q := by
    have hmod : (d + q) % 8 = (a + b) % 8 := by
      rw [ha_def, hb_def, Nat.add_mod]
    have hmod' : (d + q) % 8 = 0 := by
      rw [hmod, hsum_mod]
    exact Nat.dvd_of_mod_eq_zero hmod'
  have hqdiv : n / q = d := by
    have h1 : n / q * q = n := Nat.div_mul_cancel hqvd
    have h2 : d * q = n := by rw [mul_comm, hprod]
    have h3 : n / q * q = d * q := by rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_right hqpos h3
  refine ⟨(Nat.mem_divisors).mpr ⟨hqvd, hdne⟩, hqdiv, ?_, hdiv8⟩
  intro hne
  have hne' : q = d := hne
  have h8 : 8 ∣ d + d := by simpa [hne'] using hdiv8
  obtain ⟨k, hk⟩ := h8
  have hd4 : d = 4 * k := by omega
  have h2d : 2 ∣ d := by
    use 2 * k
    linarith
  have hde : d % 2 = 0 := Nat.mod_eq_zero_of_dvd h2d
  omega

theorem twenty_four_of_three_and_eight (x : ℕ) (h3 : 3 ∣ x) (h8 : 8 ∣ x) :
    24 ∣ x := by
  intros
  first
  | omega
  | linarith
  | positivity
  | norm_num
  | (simp_all; done)
  | ring

/--
Let $n$ be a positive integer such that $n+1$ is divisible by $24$. Prove that the sum of all the divisors of $n$ is divisible by $24$.
-/
theorem putnam_1969_b1
(n : ℕ)
(hnpos : n > 0)
(hn : 24 ∣ n + 1)
: 24 ∣ ∑ d ∈ divisors n, d := by
  obtain ⟨h3, h8⟩ := residue_from_24 n hnpos hn

  have hd3 : ∀ d ∈ divisors n,
      (n / d) ∈ divisors n ∧ n / (n / d) = d ∧ n / d ≠ d ∧ 3 ∣ d + n / d :=
    fun d hd => divisors_pair_data_mod_3 n hnpos h3 d hd

  have hd8 : ∀ d ∈ divisors n,
      (n / d) ∈ divisors n ∧ n / (n / d) = d ∧ n / d ≠ d ∧ 8 ∣ d + n / d :=
    fun d hd => divisors_pair_data_mod_8 n hnpos h8 d hd

  have hm3 : 0 < 3 := by decide
  have hm8 : 0 < 8 := by decide

  have H3 : 3 ∣ ∑ d ∈ divisors n, d :=
    sum_finset_pairing (divisors n) 3 hm3 (fun d => n / d)
      (fun d hd => (hd3 d hd).1)
      (fun d hd => (hd3 d hd).2.1)
      (fun d hd => (hd3 d hd).2.2.1)
      (fun d hd => (hd3 d hd).2.2.2)

  have H8 : 8 ∣ ∑ d ∈ divisors n, d :=
    sum_finset_pairing (divisors n) 8 hm8 (fun d => n / d)
      (fun d hd => (hd8 d hd).1)
      (fun d hd => (hd8 d hd).2.1)
      (fun d hd => (hd8 d hd).2.2.1)
      (fun d hd => (hd8 d hd).2.2.2)

  exact twenty_four_of_three_and_eight (∑ d ∈ divisors n, d) H3 H8

#print axioms putnam_1969_b1
