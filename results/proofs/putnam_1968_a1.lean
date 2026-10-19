import Mathlib


/--
Prove that $$\frac{22}{7} - \pi = \int_{0}^{1} \frac{x^4(1 - x)^4}{1 + x^2} dx$$.
-/
theorem putnam_1968_a1
: 22/7 - Real.pi = ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) := by
  let F : ℝ → ℝ := fun x => x^7/7 - (2/3)*x^6 + x^5 - (4/3)*x^3 + 4*x - 4*Real.arctan x

  have h_deriv_closed : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt F (x^4 * (1 - x)^4 / (1 + x^2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => t^7/7) (x^6) x := by
      convert (hasDerivAt_pow 7 x).const_mul (1/7) using 1
      field_simp; ring
    have h2 : HasDerivAt (fun t : ℝ => (2/3)*t^6) (4*x^5) x := by
      convert (hasDerivAt_pow 6 x).const_mul (2/3) using 1
      ring_nf
    have h3 : HasDerivAt (fun t : ℝ => t^5) (5*x^4) x := hasDerivAt_pow 5 x
    have h4 : HasDerivAt (fun t : ℝ => (4/3)*t^3) (4*x^2) x := by
      convert (hasDerivAt_pow 3 x).const_mul (4/3) using 1
      ring_nf
    have h5 : HasDerivAt (fun t : ℝ => 4*t) 4 x := by
      convert (hasDerivAt_id x).const_mul 4 using 1
      ring
    have h6 : HasDerivAt (fun t : ℝ => 4*Real.arctan t) (4/(1+x^2)) x := by
      convert (Real.hasDerivAt_arctan x).const_mul 4 using 1
      ring
    have hA : HasDerivAt (fun t : ℝ => t^7/7 - (2/3)*t^6) (x^6 - 4*x^5) x := h1.sub h2
    have hB : HasDerivAt (fun t : ℝ => t^7/7 - (2/3)*t^6 + t^5) (x^6 - 4*x^5 + 5*x^4) x := hA.add h3
    have hC : HasDerivAt (fun t : ℝ => t^7/7 - (2/3)*t^6 + t^5 - (4/3)*t^3) (x^6 - 4*x^5 + 5*x^4 - 4*x^2) x := hB.sub h4
    have hD : HasDerivAt (fun t : ℝ => t^7/7 - (2/3)*t^6 + t^5 - (4/3)*t^3 + 4*t) (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4) x := hC.add h5
    have hE : HasDerivAt (fun t : ℝ => t^7/7 - (2/3)*t^6 + t^5 - (4/3)*t^3 + 4*t - 4*Real.arctan t) (x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4/(1+x^2)) x := hD.sub h6
    have h_eq : x^6 - 4*x^5 + 5*x^4 - 4*x^2 + 4 - 4/(1+x^2) = x^4 * (1 - x)^4 / (1 + x^2) := by
      have hden : (1 : ℝ) + x^2 ≠ 0 := by positivity
      field_simp [hden]
      ring
    convert hE using 1
    · rw [h_eq]

  have hinteg : IntervalIntegrable (fun x => x^4 * (1 - x)^4 / (1 + x^2)) MeasureTheory.volume 0 1 := by
    have hcont : ContinuousOn (fun x : ℝ => x^4 * (1 - x)^4 / (1 + x^2)) (Set.Icc 0 1) := by
      have hnum : ContinuousOn (fun x : ℝ => x^4 * (1 - x)^4) (Set.Icc 0 1) := by
        apply ContinuousOn.mul
        · exact continuousOn_pow 4
        · exact (continuousOn_const.sub continuousOn_id).pow 4
      have hden : ContinuousOn (fun x : ℝ => 1 + x^2) (Set.Icc 0 1) := by
        apply ContinuousOn.add
        · exact continuousOn_const
        · exact continuousOn_pow 2
      have hden_ne : ∀ x ∈ Set.Icc (0:ℝ) 1, (1 : ℝ) + x^2 ≠ 0 := by
        intro x hx
        positivity
      exact hnum.div hden hden_ne
    refine ContinuousOn.intervalIntegrable ?_
    convert hcont using 1
    ext x
    simp [Set.uIcc, min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

  have hFTC : ∫ x in (0)..1, x^4 * (1 - x)^4 / (1 + x^2) = F 1 - F 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hinteg
    intro x hx
    have hx' : x ∈ Set.Icc (0:ℝ) 1 := by
      first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
    exact h_deriv_closed x hx'

  have hF1 : F 1 = (1:ℝ)/7 - 2/3 + 1 - 4/3 + 4 - 4*Real.arctan 1 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hF0 : F 0 = 0 := by
    simp [F]
  have h_arctan : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
  have h_val : F 1 - F 0 = 22/7 - Real.pi := by
    rw [hF1, hF0, h_arctan]
    ring
    <;> field_simp
    <;> ring

  rw [hFTC, h_val]

#print axioms putnam_1968_a1
