import Mathlib
open Topology Filter Nat Set Function


open Topology Filter Nat Set Function

noncomputable def cosGrid : Set ℝ :=
  {x | ∃ (n : ℕ) (j : ℤ), x = Real.cos (↑j * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ n))}

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

theorem f_odd (f : ℝ → ℝ) (hfcont : Continuous f)
    (hf : ∀ x, f (2 * x ^ 2 - 1) = 2 * x * f x) :
    ∀ x, f (-x) = -f x := by
  have h_odd_nonzero : ∀ x, x ≠ 0 → f (-x) = -f x := by
    intro x hx
    have h1 := hf x
    have h2 := hf (-x)
    have h_arg_eq : 2 * (-x) ^ 2 - 1 = 2 * x ^ 2 - 1 := by
      ring
    rw [h_arg_eq] at h2
    have h_eq : 2 * x * f x = 2 * (-x) * f (-x) := by
      rw [← h1, ← h2]
    have h_nonzero : (2 : ℝ) * x ≠ 0 := by
      intro h
      have : x = 0 := by
        have h2x : (2 : ℝ) * x = 0 := h
        linarith
      contradiction
    have h_sum : 2 * x * f x + 2 * x * f (-x) = 0 := by
      have : 2 * (-x) * f (-x) = -(2 * x * f (-x)) := by ring
      rw [this] at h_eq
      linarith
    have h_factored : 2 * x * (f x + f (-x)) = 0 := by
      linarith
    have h_inner_zero : f x + f (-x) = 0 := by
      apply mul_left_cancel₀ h_nonzero
      rw [mul_zero]
      exact h_factored
    linarith

  have h_f0 : f 0 = 0 := by
    let g : ℝ → ℝ := fun x => f x + f (-x)
    have hg_cont : Continuous g := by
      unfold g
      exact hfcont.add (hfcont.comp continuous_id.neg)

    have hg_zero_on_punct : ∀ x, x ≠ 0 → g x = 0 := by
      intro x hx
      unfold g
      have := h_odd_nonzero x hx
      linarith

    have h_tendsto : Filter.Tendsto g (𝓝 0) (𝓝 (g 0)) := hg_cont.tendsto 0
    have h_tendsto_punct : Filter.Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) :=
      h_tendsto.mono_left nhdsWithin_le_nhds

    have h_eq_zero : Filter.EventuallyEq (𝓝[≠] (0 : ℝ)) g (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hg_zero_on_punct x hx

    have h_tendsto_zero : Filter.Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      exact tendsto_const_nhds.congr' h_eq_zero.symm

    have h_g0 : g 0 = 0 := by
      exact tendsto_nhds_unique h_tendsto_punct h_tendsto_zero

    have : g 0 = 2 * f 0 := by
      unfold g
      ring
    rw [this] at h_g0
    linarith

  intro x
  by_cases hx : x = 0
  · subst hx
    simp [h_f0]
  · exact h_odd_nonzero x hx

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

theorem base_zero (f : ℝ → ℝ)
    (hf : ∀ x, f (2 * x ^ 2 - 1) = 2 * x * f x) :
    ∀ j : ℤ, f (Real.cos (↑j * Real.pi / (3 : ℝ))) = 0 := by
  have hf1 : f (1 : ℝ) = 0 := by
    have h := hf (1 : ℝ)
    norm_num at h
    linarith
  have hf_neg1 : f (-1 : ℝ) = 0 := by
    have h := hf (-1 : ℝ)
    norm_num at h
    rw [hf1] at h
    linarith
  have hf_neg_half : f (-(1 / 2 : ℝ)) = 0 := by
    have h := hf (-(1 / 2 : ℝ))
    norm_num at h
    linarith
  have hf_pos_half : f (1 / 2 : ℝ) = 0 := by
    have h := hf (1 / 2 : ℝ)
    norm_num at h
    rw [← h]
    exact hf_neg_half
  have hc0 : Real.cos (↑(0 : ℤ) * Real.pi / (3 : ℝ)) = (1 : ℝ) := by
    simp [Int.cast_zero]
  have hc1 : Real.cos (↑(1 : ℤ) * Real.pi / (3 : ℝ)) = (1 / 2 : ℝ) := by
    simp [Int.cast_one, Real.cos_pi_div_three]
  have hc2 : Real.cos (↑(2 : ℤ) * Real.pi / (3 : ℝ)) = -(1 / 2 : ℝ) := by
    have h : (↑(2 : ℤ) : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by
      norm_cast
      field_simp
      ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hc3 : Real.cos (↑(3 : ℤ) * Real.pi / (3 : ℝ)) = (-1 : ℝ) := by
    have h : (↑(3 : ℤ) : ℝ) * Real.pi / 3 = Real.pi := by
      norm_cast
      field_simp
    rw [h, Real.cos_pi]
  have hc4 : Real.cos (↑(4 : ℤ) * Real.pi / (3 : ℝ)) = -(1 / 2 : ℝ) := by
    have h : (↑(4 : ℤ) : ℝ) * Real.pi / 3 = Real.pi + Real.pi / 3 := by
      norm_cast
      field_simp
      ring
    rw [h]
    rw [show Real.pi + Real.pi / 3 = Real.pi / 3 + Real.pi by ring]
    rw [Real.cos_add_pi, Real.cos_pi_div_three]
  have hc5 : Real.cos (↑(5 : ℤ) * Real.pi / (3 : ℝ)) = (1 / 2 : ℝ) := by
    have h : (↑(5 : ℤ) : ℝ) * Real.pi / 3 = -(Real.pi / 3) + (1 : ℝ) * (2 * Real.pi) := by
      norm_cast
      field_simp
      ring
    rw [h]
    rw [show -(Real.pi / 3) + (1 : ℝ) * (2 * Real.pi) = -(Real.pi / 3) + (1 : ℤ) * (2 * Real.pi) by norm_cast]
    rw [Real.cos_add_int_mul_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  have hf_cos_small : ∀ (r : ℤ), 0 ≤ r → r < 6 → f (Real.cos (↑r * Real.pi / (3 : ℝ))) = 0 := by
    intro r hr0 hr1
    have hr : r ∈ Set.Ico (0 : ℤ) 6 := ⟨hr0, hr1⟩
    interval_cases r
    · rw [hc0]; exact hf1
    · rw [hc1]; exact hf_pos_half
    · rw [hc2]; exact hf_neg_half
    · rw [hc3]; exact hf_neg1
    · rw [hc4]; exact hf_neg_half
    · rw [hc5]; exact hf_pos_half
  intro j
  let q := j / 6
  let r := j % 6
  have h_eq : (6 : ℤ) * q + r = j := by
    have h := Int.emod_add_ediv j 6
    rw [add_comm] at h
    simpa [q, r] using h
  have h0 : 0 ≤ r := Int.emod_nonneg _ (by norm_num)
  have h1 : r < 6 := Int.emod_lt_of_pos _ (by norm_num)
  have h_cast : (↑j : ℝ) = (6 : ℝ) * ↑q + ↑r := by
    rw [← h_eq]
    norm_cast
  have harg : (↑j : ℝ) * Real.pi / 3 = (↑r : ℝ) * Real.pi / 3 + (↑q : ℝ) * (2 * Real.pi) := by
    rw [h_cast]
    field_simp
    ring
  have hcos : Real.cos (↑j * Real.pi / (3 : ℝ)) = Real.cos (↑r * Real.pi / (3 : ℝ)) := by
    rw [harg]
    rw [show (↑r : ℝ) * Real.pi / 3 + (↑q : ℝ) * (2 * Real.pi) = (↑r : ℝ) * Real.pi / 3 + (↑q : ℤ) * (2 * Real.pi) by norm_cast]
    rw [Real.cos_add_int_mul_two_pi]
  rw [hcos]
  exact hf_cos_small r h0 h1

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

theorem grid_zero (f : ℝ → ℝ)
    (hf : ∀ x, f (2 * x ^ 2 - 1) = 2 * x * f x)
    (h_f0 : f 0 = 0)
    (h_base : ∀ j : ℤ, f (Real.cos (↑j * Real.pi / (3 : ℝ))) = 0) :
    cosGrid ⊆ {x | f x = 0} := by
  have key : ∀ n : ℕ, ∀ j : ℤ,
      f (Real.cos ((j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ n))) = 0 := by
    intro n
    induction n with
    | zero =>
      intro j
      have hden : (j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ 0) =
          (j : ℝ) * Real.pi / (3 : ℝ) := by
        simp only [pow_zero, mul_one]
      rw [hden]
      exact h_base j
    | succ n ih =>
      intro j
      set θ := (j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ (n + 1)) with hθ
      set x := Real.cos θ with hx
      have h_arg : (2 : ℝ) * θ = (j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ n) := by
        rw [hθ]
        field_simp [pow_succ]
        ring
      have h_double : 2 * x ^ 2 - 1 =
          Real.cos ((j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ) ^ n)) := by
        rw [hx]
        rw [← Real.cos_two_mul θ]
        rw [h_arg]
      have h_mul : (2 * x) * f x = 0 := by
        rw [← hf x, h_double]
        exact ih j
      rcases mul_eq_zero.mp h_mul with h2x | hfx
      · have hx0 : x = 0 := by
          rcases mul_eq_zero.mp h2x with htwo | hx0
          · exact absurd htwo (by norm_num : (2 : ℝ) ≠ 0)
          · exact hx0
        rw [hx0]
        exact h_f0
      · exact hfx
  intro x hx
  obtain ⟨n, j, rfl⟩ := hx
  exact key n j

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

open Topology Filter Nat Set Function

lemma two_pow_ge_self_real (n : ℕ) : (n : ℝ) ≤ (2 : ℝ)^n ∧ (1 : ℝ) ≤ (2 : ℝ)^n := by
  induction n with
  | zero => constructor <;> simp
  | succ n ih =>
    constructor
    · rw [Nat.cast_succ, pow_succ]
      nlinarith [ih.1, ih.2]
    · rw [pow_succ]
      nlinarith [ih.2]

lemma exists_pow_two_gt_real (M : ℝ) : ∃ n : ℕ, M < (2 : ℝ)^n := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact ⟨n, lt_of_lt_of_le hn (two_pow_ge_self_real n).1⟩

theorem dense_cosGrid :
    closure cosGrid = Set.Icc (-1 : ℝ) 1 := by
  set A : Set ℝ := {θ | ∃ (n : ℕ) (j : ℤ), θ = (j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ)^n)}
  have hcosGrid : cosGrid = Real.cos '' A := by
    ext x
    constructor
    · rintro ⟨n, j, rfl⟩
      exact ⟨(j : ℝ) * Real.pi / ((3 : ℝ) * (2 : ℝ)^n), ⟨n, j, rfl⟩, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨n, j, rfl⟩ := hθ
      exact ⟨n, j, rfl⟩
  have hAdense : Dense A := by
    rw [Metric.dense_iff]
    intro x ε hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ)^n > Real.pi / ((3 : ℝ) * ε) :=
      exists_pow_two_gt_real (Real.pi / ((3 : ℝ) * ε))
    have hden_pos : (0 : ℝ) < (3 : ℝ) * (2 : ℝ)^n := by positivity
    set s : ℝ := Real.pi / ((3 : ℝ) * (2 : ℝ)^n) with hs_def
    have hs : (0 : ℝ) < s := by rw [hs_def]; positivity
    have hsl : s < ε := by
      have h3ε : (0 : ℝ) < (3 : ℝ) * ε := by positivity
      have key : (3 : ℝ) * ε * (2 : ℝ)^n > Real.pi := by
        have h : (3 : ℝ) * ε * (Real.pi / ((3 : ℝ) * ε)) < (3 : ℝ) * ε * (2 : ℝ)^n :=
          mul_lt_mul_of_pos_left hn h3ε
        have hc : (3 : ℝ) * ε * (Real.pi / ((3 : ℝ) * ε)) = Real.pi := by field_simp
        rwa [hc] at h
      have hgoal : ε * ((3 : ℝ) * (2 : ℝ)^n) > Real.pi := by
        have h : ε * ((3 : ℝ) * (2 : ℝ)^n) = (3 : ℝ) * ε * (2 : ℝ)^n := by ring
        rw [h]
        exact key
      rw [hs_def]
      exact (div_lt_iff₀ hden_pos).mpr hgoal
    set j : ℤ := Int.floor (x / s) + 1 with hj_def
    have hmem : (j : ℝ) * s ∈ A := by
      refine ⟨n, j, ?_⟩
      rw [hs_def]
      field_simp [hden_pos.ne']
    have hleft : x < (j : ℝ) * s := by
      have h : (x / s : ℝ) < (j : ℝ) := by
        simpa [hj_def] using Int.lt_floor_add_one (x / s)
      exact (div_lt_iff₀ hs).mp h
    have hright : (j : ℝ) * s < x + ε := by
      have h : (j : ℝ) ≤ x / s + 1 := by
        simpa [hj_def] using add_le_add_right (Int.floor_le (x / s)) 1
      have h2 : (j : ℝ) * s ≤ (x / s + 1) * s :=
        mul_le_mul_of_nonneg_right h (le_of_lt hs)
      have h3 : (x / s + 1) * s = x + s := by field_simp [hs.ne']
      rw [h3] at h2
      exact lt_of_le_of_lt h2 (add_lt_add_right hsl x)
    have hb : (j : ℝ) * s ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_pos (sub_pos.mpr hleft)]
      linarith
    exact ⟨(j : ℝ) * s, hb, hmem⟩
  have hrange : Set.range Real.cos ⊆ closure (Real.cos '' A) := by
    rw [Set.range_subset_iff]
    intro x
    exact mem_closure_image (Real.continuous_cos.continuousAt) (hAdense x)
  have hsub : Set.Icc (-1) 1 ⊆ closure cosGrid := by
    rw [hcosGrid]
    rw [← Real.range_cos]
    exact hrange
  have hsubset : cosGrid ⊆ Set.Icc (-1) 1 := by
    rintro x ⟨n, j, rfl⟩
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have htop : closure cosGrid ⊆ Set.Icc (-1) 1 :=
    closure_minimal hsubset isClosed_Icc
  exact subset_antisymm htop hsub

/--
Let $f(x)$ be a continuous function such that $f(2x^2-1)=2xf(x)$ for all $x$.  Show that $f(x)=0$ for $-1\leq x\leq 1$.
-/
theorem putnam_2000_b4
(f : ℝ → ℝ)
(hfcont : Continuous f)
(hf : ∀ x, f (2 * x ^ 2 - 1) = 2 * x * f x)
: ∀ x, x ∈ Icc (-1) 1 → f x = 0 := by
  have h_odd := f_odd f hfcont hf
  have h_f0 : f 0 = 0 := by
    have h : f 0 = -f 0 := by simpa using h_odd 0
    have h2 : (2 : ℝ) * f 0 = 0 := by
      calc
        (2 : ℝ) * f 0 = f 0 + f 0 := by ring
        _ = f 0 + -f 0 := by rw [← h]
        _ = 0 := by ring
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have h_base := base_zero f hf
  have hZ := grid_zero f hf h_f0 h_base
  have hclosed : IsClosed {x | f x = 0} := isClosed_eq hfcont continuous_const
  have hclosure := closure_mono hZ
  rw [IsClosed.closure_eq hclosed] at hclosure
  rw [dense_cosGrid] at hclosure
  intro x hx
  exact hclosure hx

#print axioms putnam_2000_b4
