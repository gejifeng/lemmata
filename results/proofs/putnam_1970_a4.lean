import Mathlib
open Metric Set EuclideanGeometry Filter Topology


open Metric Set EuclideanGeometry Filter Topology

open Metric Set EuclideanGeometry Filter Topology

/--
Suppose $(x_n)$ is a sequence such that $\lim_{n \to \infty} (x_n - x_{n-2} = 0$. Prove that $\lim_{n \to \infty} \frac{x_n - x_{n-1}}{n} = 0$.
-/
theorem putnam_1970_a4
(x : ℕ → ℝ)
(hxlim : Tendsto (fun n => x (n+2) - x n) atTop (𝓝 0))
: Tendsto (fun n => (x (n+1) - x (n))/(n+1)) atTop (𝓝 0) := by
  let y : ℕ → ℝ := fun n => (-1 : ℝ)^n * (x (n+1) - x n)
  let d : ℕ → ℝ := fun n => y (n+1) - y n

  have hd_eq : ∀ n, d n = (-1 : ℝ)^(n+1) * (x (n+2) - x n) := by
    intro n
    dsimp only [d, y]
    rw [pow_succ]
    ring

  have hd : Tendsto d atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => ‖x (n+2) - x n‖) atTop (𝓝 0) := by
      simpa using hxlim.norm
    have hseq : (fun n => ‖d n‖) = (fun n => ‖x (n+2) - x n‖) := by
      ext n
      rw [hd_eq, norm_mul, norm_pow]
      rw [norm_neg, norm_one, one_pow, one_mul]
    rw [← hseq] at hnorm
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm

  have hsum : ∀ n, y n = y 0 + ∑ i ∈ Finset.range n, d i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hy : y (n+1) = y n + d n := by
        dsimp [d]
        linarith
      rw [hy, ih]
      ring

  have hCes : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, d i) atTop (𝓝 0) :=
    hd.cesaro

  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop_atTop.mpr ?_
    intro N
    obtain ⟨M, hM⟩ := exists_nat_gt N
    use M
    intro n hn
    have h2 : (M : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have h3 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h4 : (N : ℝ) < (M : ℝ) := by exact_mod_cast hM
    linarith

  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1

  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / (↑n + 1)) atTop (𝓝 1) := by
    have : (fun n : ℕ => (n : ℝ) / (↑n + 1)) = (fun n : ℕ => 1 - ((n : ℝ) + 1)⁻¹) := by
      ext n
      have hne : (n : ℝ) + 1 ≠ 0 := by
        have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        linarith
      field_simp [hne]
      try ring
    rw [this]
    simpa using tendsto_const_nhds.sub hinv

  have hCes1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.range n, d i) atTop (𝓝 0) := by
    have : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.range n, d i)
        = (fun n : ℕ => ((n : ℝ) / (↑n + 1)) * ((↑n)⁻¹ * ∑ i ∈ Finset.range n, d i)) := by
      ext n
      rcases n with _|m
      · simp
      · push_cast
        field_simp
        try ring
    rw [this]
    simpa using hfrac.mul hCes

  have hY : Tendsto (fun n : ℕ => y n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => y n / ((n : ℝ) + 1)) = (fun n : ℕ => (y 0) * ((n : ℝ) + 1)⁻¹ + ((n : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.range n, d i) := by
      ext n
      rw [hsum, div_eq_mul_inv]
      try ring
    rw [heq]
    have h_const0 : Tendsto (fun n : ℕ => (y 0) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinv
    have h_sum : Tendsto (fun n : ℕ => (y 0) * ((n : ℝ) + 1)⁻¹ + ((n : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.range n, d i) atTop (𝓝 (0 + 0)) :=
      h_const0.add hCes1
    convert h_sum using 1
    simp

  have hgoal : Tendsto (fun n : ℕ => ((-1 : ℝ)^n * (y n / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n : ℕ => ‖y n / ((n : ℝ) + 1)‖) atTop (𝓝 0) := by
      simpa using hY.norm
    have hseq : (fun n : ℕ => ‖((-1 : ℝ)^n * (y n / ((n : ℝ) + 1)))‖) = (fun n : ℕ => ‖y n / ((n : ℝ) + 1)‖) := by
      ext n
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [← hseq] at hnorm
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm

  have heq_goal : (fun n : ℕ => (x (n+1) - x n) / (n + 1 : ℝ)) = (fun n : ℕ => ((-1 : ℝ)^n * (y n / ((n : ℝ) + 1)))) := by
    ext n
    dsimp only [y]
    have hp : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
      have h : n + n = 2 * n := by ring
      rw [← pow_add, h, pow_mul]
      simp
    calc
      (x (n+1) - x n) / ((n : ℝ) + 1)
          = ((-1 : ℝ)^n * (-1 : ℝ)^n * (x (n+1) - x n)) / ((n : ℝ) + 1) := by
            rw [hp, one_mul]
      _ = (-1 : ℝ)^n * (((-1 : ℝ)^n * (x (n+1) - x n)) / ((n : ℝ) + 1)) := by
        simp only [div_eq_mul_inv]
        try ring
      _ = (-1 : ℝ)^n * (y n / ((n : ℝ) + 1)) := rfl

  rw [heq_goal]
  exact hgoal

#print axioms putnam_1970_a4
