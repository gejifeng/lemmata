import Mathlib
open Complex


open Complex

open Complex

open Complex

open Complex

open Complex

theorem putnam_1989_a3_norm_sq_identities (z : ℂ) :
    (‖11 * z + 10 * I‖ ^ 2 = 121 * ‖z‖ ^ 2 + 100 + 220 * z.im ∧
     ‖11 - 10 * I * z‖ ^ 2 = 121 + 100 * ‖z‖ ^ 2 + 220 * z.im) := by
  have norm_sq_eq_re_im (w : ℂ) : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [pow_two, Complex.norm_def, Complex.normSq_apply, ← sq, Real.sq_sqrt]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  constructor
  · rw [norm_sq_eq_re_im, norm_sq_eq_re_im]
    have hre : (11 * z + 10 * I).re = 11 * z.re := by
      have h11 : (11 : ℂ) = (11 : ℝ) := by norm_cast
      have h10 : (10 : ℂ) = (10 : ℝ) := by norm_cast
      rw [h11, h10]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.add_re]
    have him : (11 * z + 10 * I).im = 11 * z.im + 10 := by
      have h11 : (11 : ℂ) = (11 : ℝ) := by norm_cast
      have h10 : (10 : ℂ) = (10 : ℝ) := by norm_cast
      rw [h11, h10]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.add_im]
    rw [hre, him]
    ring
  · rw [norm_sq_eq_re_im, norm_sq_eq_re_im]
    have hre : (11 - 10 * I * z).re = 11 + 10 * z.im := by
      have h11 : (11 : ℂ) = (11 : ℝ) := by norm_cast
      have h10 : (10 : ℂ) = (10 : ℝ) := by norm_cast
      rw [h11, h10]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.sub_re]
    have him : (11 - 10 * I * z).im = -10 * z.re := by
      have h11 : (11 : ℂ) = (11 : ℝ) := by norm_cast
      have h10 : (10 : ℂ) = (10 : ℝ) := by norm_cast
      rw [h11, h10]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.sub_im]
    rw [hre, him]
    ring

open Complex

open Complex

theorem putnam_1989_a3_norm_sq_relation (z : ℂ)
    (hz : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0)
    (hids : (‖11 * z + 10 * I‖ ^ 2 = 121 * ‖z‖ ^ 2 + 100 + 220 * z.im ∧
             ‖11 - 10 * I * z‖ ^ 2 = 121 + 100 * ‖z‖ ^ 2 + 220 * z.im)) :
    ‖z‖ ^ 18 * (121 * ‖z‖ ^ 2 + 100 + 220 * z.im) =
      121 + 100 * ‖z‖ ^ 2 + 220 * z.im := by
  have hfac : z ^ 9 * (11 * z + 10 * I) = 11 - 10 * I * z := by
    have hdiff : z ^ 9 * (11 * z + 10 * I) - (11 - 10 * I * z) = 0 := by
      have h : z ^ 9 * (11 * z + 10 * I) - (11 - 10 * I * z) =
          11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 := by ring
      rw [h]
      exact hz
    exact sub_eq_zero.mp hdiff
  have hnorm : ‖z ^ 9 * (11 * z + 10 * I)‖ ^ 2 = ‖11 - 10 * I * z‖ ^ 2 := by
    rw [hfac]
  rw [norm_mul, mul_pow, norm_pow] at hnorm
  rw [← pow_mul (‖z‖) 9 2] at hnorm
  rw [show ((9 : ℕ) * 2 = 18) by norm_num] at hnorm
  obtain ⟨h1, h2⟩ := hids
  rw [h1, h2] at hnorm
  exact hnorm

theorem putnam_1989_a3_key_identity (r y : ℝ)
    (h : r ^ 18 * (121 * r ^ 2 + 100 + 220 * y) =
        121 + 100 * r ^ 2 + 220 * y) :
    (121 * r ^ 2 + 100 + 220 * y) * (r ^ 18 - 1) =
      -21 * (r ^ 2 - 1) := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

theorem putnam_1989_a3_norm_pos (z : ℂ)
    (hz : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0) :
    0 < ‖z‖ := by
  intros
  first
  | (grind; done)
  | (aesop; done)
  | ((nlinarith [sq_nonneg (0:ℝ)]); done)
  | ((field_simp; ring); done)
  | ((norm_num; ring_nf); done)
  | ((simp_all; ring_nf); done)
  | ((push_cast; ring); done)

open Complex

theorem putnam_1989_a3_A_nonneg (z : ℂ) :
    0 ≤ 121 * ‖z‖ ^ 2 + 100 + 220 * z.im := by
  have h : 121 * ‖z‖ ^ 2 + 100 + 220 * z.im =
      121 * z.re ^ 2 + (11 * z.im + 10) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [h]
  positivity

open Complex

open Complex

open Complex

open Complex

open Complex

open Complex

open Complex

theorem putnam_1989_a3_sign_contradiction (r y : ℝ)
    (hr : 0 < r)
    (hr_ne : r ≠ 1)
    (hkey : (121 * r ^ 2 + 100 + 220 * y) * (r ^ 18 - 1) =
            -21 * (r ^ 2 - 1))
    (hA : 0 ≤ 121 * r ^ 2 + 100 + 220 * y) : False := by
  set A := 121 * r ^ 2 + 100 + 220 * y with hAdef
  set S := ∑ k ∈ Finset.range 9, (r ^ 2) ^ k with hSdef
  have hfac : r ^ 18 - 1 = (r ^ 2 - 1) * S := by
    have hgeom := geom_sum_mul (r ^ 2) 9
    have h1 : (r ^ 2 - 1) * S = (r ^ 2) ^ 9 - 1 := by
      rw [mul_comm, hgeom]
    rw [h1]
    have : (r ^ 2) ^ 9 = r ^ 18 := by ring
    rw [this]
  rw [hfac] at hkey
  have hzero : (r ^ 2 - 1) * (A * S + 21) = 0 := by
    have h1 : A * ((r ^ 2 - 1) * S) + 21 * (r ^ 2 - 1) = 0 := by
      rw [hkey]
      ring
    have h2 : (r ^ 2 - 1) * (A * S + 21) = A * ((r ^ 2 - 1) * S) + 21 * (r ^ 2 - 1) := by
      ring
    rw [h2, h1]
  have hne : r ^ 2 - 1 ≠ 0 := by
    intro h
    have hsq : r ^ 2 = 1 := by linarith
    have hprod : (r - 1) * (r + 1) = 0 := by
      nlinarith
    have hcases : r - 1 = 0 ∨ r + 1 = 0 := mul_eq_zero.mp hprod
    cases hcases with
    | inl hc =>
      have : r = 1 := by linarith
      exact hr_ne this
    | inr hc =>
      have : r = -1 := by linarith
      have : r > 0 := hr
      linarith
  have hAS : A * S + 21 = 0 := by
    have hcases : r ^ 2 - 1 = 0 ∨ A * S + 21 = 0 := mul_eq_zero.mp hzero
    cases hcases with
    | inl hc => exact absurd hc hne
    | inr hc => exact hc
  have hSpos : 0 < S := by
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range 8, (r ^ 2) ^ (k + 1) := by
      apply Finset.sum_nonneg
      intro k _
      exact pow_nonneg (sq_nonneg r) (k + 1)
    have hexpand : S = 1 + ∑ k ∈ Finset.range 8, (r ^ 2) ^ (k + 1) := by
      rw [hSdef]
      rw [Finset.sum_range_succ']
      simp [pow_zero]
      ring
    rw [hexpand]
    linarith
  have hASnonneg : 0 ≤ A * S := mul_nonneg hA (le_of_lt hSpos)
  have hASval : A * S = -21 := by linarith
  linarith

/--
Prove that if
\[
11z^{10}+10iz^9+10iz-11=0,
\]
then $|z|=1.$ (Here $z$ is a complex number and $i^2=-1$.)
-/
theorem putnam_1989_a3
(z : ℂ)
(hz : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0)
: (‖z‖ = 1) := by
  have hids := putnam_1989_a3_norm_sq_identities z
  have hrel := putnam_1989_a3_norm_sq_relation z hz hids
  have hkey := putnam_1989_a3_key_identity ‖z‖ z.im hrel
  have hA := putnam_1989_a3_A_nonneg z
  have hr := putnam_1989_a3_norm_pos z hz
  by_contra hne
  exact putnam_1989_a3_sign_contradiction ‖z‖ z.im hr hne hkey hA

#print axioms putnam_1989_a3
