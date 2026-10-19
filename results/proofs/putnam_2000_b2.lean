import Mathlib
open Topology Filter Nat


open Topology Filter Nat

lemma factorial_pred_mul {k : ℕ} (hk : 1 ≤ k) :
    Nat.factorial (k - 1) * k = Nat.factorial k := by
  cases k with
  | zero =>
      have hFalse : False := by omega
      exact hFalse.elim
  | succ j =>
      have hsub : Nat.succ j - 1 = j := by omega
      rw [hsub, Nat.factorial_succ]
      ring

lemma factorial_mul_pred {k : ℕ} (hk : 1 ≤ k) :
    k * Nat.factorial (k - 1) = Nat.factorial k := by
  rw [Nat.mul_comm, factorial_pred_mul hk]

theorem putnam_2000_b2_choose_identity
    (m n : ℕ) (hm : 1 ≤ m) (hn : m ≤ n) :
    m * Nat.choose n m = n * Nat.choose (n - 1) (m - 1) := by
  have h1 : (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (m * Nat.choose n m) = Nat.factorial n := by
    calc (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (m * Nat.choose n m)
        = Nat.choose n m * (Nat.factorial (m - 1) * m) * Nat.factorial (n - m) := by ring
      _ = Nat.choose n m * Nat.factorial m * Nat.factorial (n - m) := by
          rw [factorial_pred_mul hm]
      _ = Nat.factorial n := Nat.choose_mul_factorial_mul_factorial hn
  have h2 : (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (n * Nat.choose (n - 1) (m - 1)) = Nat.factorial n := by
    have hsub : n - m = (n - 1) - (m - 1) := by omega
    calc (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (n * Nat.choose (n - 1) (m - 1))
        = n * (Nat.choose (n - 1) (m - 1) * Nat.factorial (m - 1) * Nat.factorial (n - m)) := by ring
      _ = n * (Nat.choose (n - 1) (m - 1) * Nat.factorial (m - 1) * Nat.factorial ((n - 1) - (m - 1))) := by
          rw [hsub]
      _ = n * Nat.factorial (n - 1) := by
          rw [Nat.choose_mul_factorial_mul_factorial (by omega : m - 1 ≤ n - 1)]
      _ = Nat.factorial n := factorial_mul_pred (Nat.le_trans hm hn)
  have hD : 0 < Nat.factorial (m - 1) * Nat.factorial (n - m) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h : (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (m * Nat.choose n m)
      = (Nat.factorial (m - 1) * Nat.factorial (n - m)) * (n * Nat.choose (n - 1) (m - 1)) := h1.trans h2.symm
  exact Nat.eq_of_mul_eq_mul_left hD h

theorem putnam_2000_b2_cancel_pos_mul
    (d x y : ℕ) (hd : 1 ≤ d) (h : d * x = d * y) : x = y := by
  intros
  first
  | grind
  | aesop
  | (nlinarith [sq_nonneg (0:ℝ)])
  | (field_simp; ring)
  | decide

open Topology Filter Nat

theorem putnam_2000_b2_gcd_decompose
    (m n : ℕ) (hm : 1 ≤ m) (hn : m ≤ n) :
    ∃ d a b : ℕ,
      1 ≤ d ∧
      m = d * a ∧
      n = d * b ∧
      Nat.Coprime a b ∧
      Nat.gcd m n = d := by
  set d := Nat.gcd m n with hd_def
  set a := m / d with ha_def
  set b := n / d with hb_def

  have hd0 : d ≠ 0 := by
    intro h
    rw [hd_def, Nat.gcd_eq_zero_iff] at h
    omega

  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)

  have hdm : d ∣ m := by
    rw [hd_def]
    exact Nat.gcd_dvd_left m n

  have hdn : d ∣ n := by
    rw [hd_def]
    exact Nat.gcd_dvd_right m n

  have hma : m = d * a := by
    rw [ha_def]
    exact (Nat.mul_div_cancel' hdm).symm

  have hnb : n = d * b := by
    rw [hb_def]
    exact (Nat.mul_div_cancel' hdn).symm

  have hga : a * d = m := by
    rw [Nat.mul_comm, hma]

  have hgb : b * d = n := by
    rw [Nat.mul_comm, hnb]

  have hgcd_eq : Nat.gcd a b * d = d := by
    rw [← Nat.gcd_mul_right a d b, hga, hgb, hd_def]

  have hcancel : d * Nat.gcd a b = d * 1 := by
    rw [Nat.mul_one, Nat.mul_comm, hgcd_eq]

  have hcop_gcd : Nat.gcd a b = 1 :=
    putnam_2000_b2_cancel_pos_mul d (Nat.gcd a b) 1 hd1 hcancel

  refine ⟨d, a, b, hd1, hma, hnb, ?_, hd_def.symm⟩
  exact hcop_gcd

theorem putnam_2000_b2_coprime_mul_left_dvd
    (a b c t : ℕ) (hcop : Nat.Coprime a b) (h : a * c = b * t) : b ∣ c := by
  have hb : b ∣ a * c := ⟨t, h⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hb

theorem putnam_2000_b2_mul_dvd_mul_left
    (d b c : ℕ) (h : b ∣ c) : d * b ∣ d * c := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by ring⟩

/--
Prove that the expression
\[
\frac{gcd(m,n)}{n}\binom{n}{m}
\]
is an integer for all pairs of integers $n\geq m\geq 1$.
-/
theorem putnam_2000_b2
: (∀ m n : ℕ, m ≥ 1 → n ≥ m → n ∣ Nat.gcd m n * Nat.choose n m) := by
  intro m n hm hn
  obtain ⟨d, a, b, hd_pos, hm_eq, hn_eq, hcop, hd_gcd⟩ :=
    putnam_2000_b2_gcd_decompose m n hm hn
  have hchoose := putnam_2000_b2_choose_identity m n hm hn
  rw [hm_eq, hn_eq] at hchoose
  simp only [mul_assoc] at hchoose
  have hab :=
    putnam_2000_b2_cancel_pos_mul d
      (a * Nat.choose (d * b) (d * a))
      (b * Nat.choose (d * b - 1) (d * a - 1)) hd_pos hchoose
  have hb : b ∣ Nat.choose (d * b) (d * a) :=
    putnam_2000_b2_coprime_mul_left_dvd a b
      (Nat.choose (d * b) (d * a))
      (Nat.choose (d * b - 1) (d * a - 1)) hcop hab
  rw [hd_gcd, hn_eq, hm_eq]
  exact putnam_2000_b2_mul_dvd_mul_left d b (Nat.choose (d * b) (d * a)) hb

#print axioms putnam_2000_b2
