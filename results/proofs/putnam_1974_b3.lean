import Mathlib
open Set Nat Polynomial Filter Topology


theorem niven_cos_values (θ : ℝ)
    (hθ : ∃ r : ℚ, θ = (r : ℝ) * Real.pi)
    (hcos : ∃ q : ℚ, Real.cos θ = (q : ℝ)) :
    Real.cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  intros
  exact niven hθ hcos

theorem one_third_eq_rat_cast :
    (1 : ℝ) / 3 = (↑((1 : ℚ) / (3 : ℚ)) : ℝ) := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

theorem one_third_not_niven_values :
    (1 : ℝ) / 3 ∉ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

/--
Prove that if $\alpha$ is a real number such that $\cos (\pi \alpha) = 1/3$, the $\alpha$ is irrational.
-/
theorem putnam_1974_b3
(α : ℝ)
(ha : Real.cos (Real.pi * α) = (1 : ℝ)/3)
: Irrational α := by
  intro hα
  obtain ⟨q, hq⟩ := hα
  subst hq
  rw [mul_comm Real.pi (q : ℝ)] at ha
  have hθ : ∃ r : ℚ, (q : ℝ) * Real.pi = (r : ℝ) * Real.pi := ⟨q, rfl⟩
  have hcos : ∃ r : ℚ, Real.cos ((q : ℝ) * Real.pi) = (r : ℝ) :=
    ⟨(1 : ℚ) / (3 : ℚ), ha.trans one_third_eq_rat_cast⟩
  have hmem := niven_cos_values ((q : ℝ) * Real.pi) hθ hcos
  rw [ha] at hmem
  exact one_third_not_niven_values hmem

#print axioms putnam_1974_b3
