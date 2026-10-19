import Mathlib
open Nat Set MeasureTheory Topology Filter


/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

theorem pow_rat_coords (z : ℂ) (hz : ∃ q1 q2 : ℚ, z.re = q1 ∧ z.im = q2) (k : ℕ) :
    ∃ q1 q2 : ℚ, (z ^ k).re = q1 ∧ (z ^ k).im = q2 := by
  rcases hz with ⟨r, s, hr, hs⟩
  induction k with
  | zero =>
      refine ⟨1, 0, ?_, ?_⟩
      · rw [pow_zero, Complex.one_re]
        norm_cast
      · rw [pow_zero, Complex.one_im]
        norm_cast
  | succ n ih =>
      obtain ⟨a, b, ha, hb⟩ := ih
      refine ⟨a * r - b * s, a * s + b * r, ?_, ?_⟩
      · rw [pow_succ, Complex.mul_re, ha, hb, hr, hs]
        push_cast
        ring
      · rw [pow_succ, Complex.mul_im, ha, hb, hr, hs]
        push_cast
        ring

theorem norm_pow_eq_one (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) : ‖z ^ k‖ = 1 := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

open Nat Set MeasureTheory Topology Filter


/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

open Nat Set MeasureTheory Topology Filter


/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

theorem norm_sq_sub_one_rat (w : ℂ) (hw : ∃ q1 q2 : ℚ, w.re = q1 ∧ w.im = q2) (hwn : ‖w‖ = 1) :
    ∃ q : ℚ, ‖w ^ 2 - 1‖ = q := by
  obtain ⟨a, b, ha, hb⟩ := hw
  set A : ℝ := (a : ℝ) with hA
  set B : ℝ := (b : ℝ) with hB
  have hsum : A ^ 2 + B ^ 2 = 1 := by
    have h : ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
    rw [hwn] at h
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1] at h
    rw [Complex.normSq_apply, ha, hb] at h
    linarith
  have hre : (w ^ 2 - 1).re = -2 * B ^ 2 := by
    have h1 : (w ^ 2).re = A ^ 2 - B ^ 2 := by
      rw [pow_two, Complex.mul_re, ha, hb]
      ring
    rw [Complex.sub_re, h1]
    have hA2 : A ^ 2 = 1 - B ^ 2 := by linarith
    have h1' : Complex.re (1 : ℂ) = (1 : ℝ) := Complex.one_re
    simp only [h1']
    linarith
  have him : (w ^ 2 - 1).im = 2 * A * B := by
    have h1 : (w ^ 2).im = 2 * A * B := by
      rw [pow_two, Complex.mul_im, ha, hb]
      ring
    rw [Complex.sub_im, h1]
    simp
  have hnormSq : Complex.normSq (w ^ 2 - 1) = 4 * B ^ 2 := by
    have key : (-2 * B ^ 2) ^ 2 + (2 * A * B) ^ 2 = 4 * B ^ 2 := by
      calc (-2 * B ^ 2) ^ 2 + (2 * A * B) ^ 2
          = 4 * B ^ 2 * (A ^ 2 + B ^ 2) := by ring
        _ = 4 * B ^ 2 * 1 := by rw [hsum]
        _ = 4 * B ^ 2 := by ring
    rw [Complex.normSq_apply, hre, him]
    rw [← key]
    ring
  have hnorm : ‖w ^ 2 - 1‖ = 2 * |B| := by
    have hsq : ‖w ^ 2 - 1‖ ^ 2 = (2 * |B| : ℝ) ^ 2 := by
      calc ‖w ^ 2 - 1‖ ^ 2 = Complex.normSq (w ^ 2 - 1) := (Complex.normSq_eq_norm_sq (w ^ 2 - 1)).symm
        _ = 4 * B ^ 2 := hnormSq
        _ = (2 * |B| : ℝ) ^ 2 := by
            have h : (2 * |B| : ℝ) ^ 2 = 4 * B ^ 2 := by
              first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
            rw [h]
    have hpos : 0 ≤ ‖w ^ 2 - 1‖ := norm_nonneg _
    have hpos2 : 0 ≤ (2 * |B| : ℝ) := by positivity
    nlinarith [sq_abs (‖w ^ 2 - 1‖ - 2 * |B|)]
  use 2 * |b|
  have cast_eq : ((2 * |b| : ℚ) : ℝ) = 2 * |B| := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  rw [hnorm, cast_eq]

theorem z_ne_zero_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  rw [h, norm_zero] at hz
  exact absurd hz (by norm_num)

open Nat Set MeasureTheory Topology Filter


/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

open Nat Set MeasureTheory Topology Filter

/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

theorem even_zpow_eq_pow_sq_ofNat (z : ℂ) (k : ℕ) :
    z ^ (2 * (Int.ofNat k)) = (z ^ k) ^ 2 := by
  have h : (2 : ℤ) * (Int.ofNat k) = Int.ofNat (2 * k) := by
    norm_cast
  rw [h]
  rw [show z ^ (Int.ofNat (2 * k)) = z ^ (2 * k) from rfl]
  rw [pow_two, ← pow_add, ← Nat.two_mul]

open Nat Set MeasureTheory Topology Filter


/-!
Informal proof sketch.

Write z = x + iy with x, y ∈ ℚ and ‖z‖ = 1.

For k ∈ ℕ, let w = z^k. By induction, w has rational coordinates, say w = a + ib with a, b ∈ ℚ.
Also ‖w‖ = ‖z‖^k = 1, hence a^2 + b^2 = 1.

Now
  w^2 - 1 = (a^2 - b^2 - 1) + 2abi.
Using a^2 + b^2 = 1, the real part simplifies to -2b^2, so
  ‖w^2 - 1‖^2 = (-2b^2)^2 + (2ab)^2 = 4b^2(a^2 + b^2) = 4b^2.
Therefore ‖w^2 - 1‖ = 2|b| ∈ ℚ. Since z^(2k) = (z^k)^2 = w^2, this proves the result for n ≥ 0.

For n < 0, write n = -(k+1) with k ∈ ℕ. Since ‖z‖ = 1, z ≠ 0. Then
  z^(-2(k+1)) - 1 = z^(-2(k+1)) * (1 - z^(2(k+1))),
and taking norms gives
  ‖z^(-2(k+1)) - 1‖ = ‖z^(-2(k+1))‖ · ‖1 - z^(2(k+1))‖
                    = 1 · ‖z^(2(k+1)) - 1‖,
which is rational by the positive case.
-/

open Nat Set MeasureTheory Topology Filter

theorem negSucc_even_zpow_norm_eq (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖z ^ (2 * Int.negSucc k) - 1‖ = ‖z ^ (2 * Int.ofNat (k + 1)) - 1‖ := by
  set A := z ^ (2 * Int.ofNat (k + 1)) with hAdef
  have hAn : ‖A‖ = 1 := by
    rw [hAdef, even_zpow_eq_pow_sq_ofNat]
    have hB : ‖z ^ (k + 1)‖ = 1 := norm_pow_eq_one z hz (k + 1)
    rw [norm_pow, hB, one_pow]
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, norm_zero] at hAn
    exact absurd hAn (by norm_num)
  have hexp : (2 : ℤ) * Int.negSucc k = - (2 * Int.ofNat (k + 1)) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have h_id : A⁻¹ - 1 = A⁻¹ * (1 - A) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  calc
    ‖z ^ (2 * Int.negSucc k) - 1‖
      = ‖A⁻¹ - 1‖ := by
        rw [hexp, zpow_neg, ← hAdef]
    _ = ‖A⁻¹ * (1 - A)‖ := by rw [h_id]
    _ = ‖A⁻¹‖ * ‖1 - A‖ := by rw [norm_mul]
    _ = ‖A‖⁻¹ * ‖A - 1‖ := by rw [norm_inv, norm_sub_rev]
    _ = ‖A - 1‖ := by rw [hAn, inv_one, one_mul]
    _ = ‖z ^ (2 * Int.ofNat (k + 1)) - 1‖ := by rw [hAdef]

/--
Let $z = x+iy$ be a complex number with $x$ and $y$ rational and with $\| z \| = 1$. Show thaat the number $\| z^{2n} - 1 \|$ is rational for every integer $n$.
-/
theorem putnam_1973_b2
(z : ℂ)
(hzrat : ∃ q1 q2 : ℚ, z.re = q1 ∧ z.im = q2)
(hznorm : ‖z‖ = 1)
: ∀ n : ℤ, ∃ q : ℚ, ‖z^(2*n) - 1‖ = q := by
  intro n
  cases n with
  | ofNat k =>
      obtain ⟨a, b, ha, hb⟩ := pow_rat_coords z hzrat k
      have hw : ‖z ^ k‖ = 1 := norm_pow_eq_one z hznorm k
      obtain ⟨q, hq⟩ := norm_sq_sub_one_rat (z ^ k) ⟨a, b, ha, hb⟩ hw
      use q
      have h := even_zpow_eq_pow_sq_ofNat z k
      have hnorm := congr_arg (fun t : ℂ => ‖t - 1‖) h
      exact hnorm.trans hq
  | negSucc k =>
      have hz0 : z ≠ 0 := z_ne_zero_of_norm_eq_one z hznorm
      obtain ⟨a, b, ha, hb⟩ := pow_rat_coords z hzrat (k + 1)
      have hw : ‖z ^ (k + 1)‖ = 1 := norm_pow_eq_one z hznorm (k + 1)
      obtain ⟨q, hq⟩ := norm_sq_sub_one_rat (z ^ (k + 1)) ⟨a, b, ha, hb⟩ hw
      use q
      have h := negSucc_even_zpow_norm_eq z hz0 hznorm k
      have hexp := even_zpow_eq_pow_sq_ofNat z (k + 1)
      have hnorm := congr_arg (fun t : ℂ => ‖t - 1‖) hexp
      exact h.trans (hnorm.trans hq)

#print axioms putnam_1973_b2
