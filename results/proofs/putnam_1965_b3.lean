import Mathlib
open EuclideanGeometry Topology Filter Complex


open EuclideanGeometry Topology Filter Complex

theorem putnam_rat_eq_iff (a b c : ℤ) :
    (a * b / (2 : ℚ) = 2 * (a + b + c)) ↔ a * b = 4 * (a + b + c) := by
  constructor
  · intro h
    rw [div_eq_iff (show (2 : ℚ) ≠ 0 by norm_num)] at h
    rw [show (2 : ℚ) * (a + b + c : ℚ) * 2 = (4 : ℚ) * (a + b + c : ℚ) by ring] at h
    have h2 : (a * b : ℚ) = (4 * (a + b + c) : ℚ) := by simpa using h
    exact_mod_cast h2
  · intro h
    have h1 : ((a * b : ℤ) : ℚ) = ((4 * (a + b + c) : ℤ) : ℚ) := by exact_mod_cast h
    have h2 : (a * b : ℚ) = ((a * b : ℤ) : ℚ) := by simp
    calc
      (a * b : ℚ) / 2 = ((4 * (a + b + c) : ℤ) : ℚ) / 2 := by rw [← h1, h2]
      _ = (4 : ℚ) * (a + b + c : ℚ) / 2 := by push_cast; rfl
      _ = 2 * (a + b + c : ℚ) := by field_simp; ring

open EuclideanGeometry Topology Filter Complex

theorem putnam_bounds (a b c : ℤ) (ha : a > 0) (hab : a ≤ b) (hc : c > 0)
    (hp : a^2 + b^2 = c^2) (harea : a * b = 4 * (a + b + c)) :
    9 ≤ a ∧ a < 16 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hc4 : 4 * c = a * b - 4 * (a + b) := by linarith [harea]
  have hp2 : c * c = a * a + b * b := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hsq : (a * b - 4 * (a + b)) ^ 2 = 16 * (a * a + b * b) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hzero_poly :
      (a * b - 4 * (a + b)) ^ 2 - 16 * (a + b) ^ 2 + 32 * (a * b) = 0 := by
    rw [hsq]
    ring
  have hfactor : (a * b) * (a * b - 8 * (a + b) + 32) = 0 := by
    have hf :
        (a * b - 4 * (a + b)) ^ 2 - 16 * (a + b) ^ 2 + 32 * (a * b)
          = (a * b) * (a * b - 8 * (a + b) + 32) := by ring
    rw [hf] at hzero_poly
    exact hzero_poly
  have hsecond_zero : a * b - 8 * (a + b) + 32 = 0 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hfactor with h1 | h2
    · exact absurd h1 (ne_of_gt hab_pos)
    · exact h2
  have hab_eq : a * b = 8 * (a + b) - 32 := by linarith [hsecond_zero]
  have hprod : (a - 8) * (b - 8) = 32 := by
    calc
      (a - 8) * (b - 8) = a * b - 8 * (a + b) + 64 := by ring
      _ = (8 * (a + b) - 32) - 8 * (a + b) + 64 := by rw [hab_eq]
      _ = 32 := by ring
  have hc_eq : c = a + b - 8 := by
    have h : 4 * c = 4 * (a + b - 8) := by
      rw [hc4, hab_eq]
      ring
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h
  have hcb : b < c := by
    have hsqdiff : (c - b) * (c + b) = a * a := by
      calc
        (c - b) * (c + b) = c * c - b * b := by ring
        _ = (a * a + b * b) - b * b := by rw [hp2]
        _ = a * a := by ring
    have hsum_pos : 0 < c + b := add_pos hc hb
    have ha_sq_pos : 0 < a * a := mul_pos ha ha
    by_contra hnot
    push_neg at hnot
    have hdiff_nonpos : c - b ≤ 0 := by linarith
    have hprod_nonpos : (c - b) * (c + b) ≤ 0 := by
      have := mul_le_mul_of_nonneg_right hdiff_nonpos (le_of_lt hsum_pos)
      simpa using this
    linarith [hsqdiff, ha_sq_pos, hprod_nonpos]
  have ha_ge_9 : 9 ≤ a := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have ha_lt_16 : a < 16 := by
    by_contra hnot
    push_neg at hnot
    have hxa : 8 ≤ a - 8 := by linarith
    have hxb : 8 ≤ b - 8 := by linarith [hab]
    have hy0 : 0 ≤ b - 8 := by linarith
    have hge64 : (a - 8) * (b - 8) ≥ 64 := by
      calc
        (64 : ℤ) = 8 * 8 := by norm_num
        _ ≤ 8 * (b - 8) := by
          refine mul_le_mul_of_nonneg_left hxb ?_
          norm_num
        _ ≤ (a - 8) * (b - 8) := by
          refine mul_le_mul_of_nonneg_right hxa hy0
    linarith [hprod]
  exact ⟨ha_ge_9, ha_lt_16⟩

theorem putnam_b_linear (a b c : ℤ) (hb : b > 0)
    (hp : a^2 + b^2 = c^2) (harea : a * b = 4 * (a + b + c)) :
    (a^2 - 8 * a) * b = 8 * a * (a - 4) := by
  have hc4 : a * b - 4 * a - 4 * b = 4 * c := by
    rw [harea]
    ring
  have hsq : (a * b - 4 * a - 4 * b)^2 = 16 * a^2 + 16 * b^2 := by
    rw [hc4]
    have h4 : (4 * c)^2 = 16 * c^2 := by ring
    rw [h4]
    rw [← hp]
    ring
  have hfac : (a * b - 4 * a - 4 * b)^2 - 16 * a^2 - 16 * b^2 =
      a * b * (a * b - 8 * a - 8 * b + 32) := by ring
  have hprod : a * b * (a * b - 8 * a - 8 * b + 32) = 0 := by
    rw [← hfac]
    rw [hsq]
    ring
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hzero : a * (a * b - 8 * a - 8 * b + 32) = 0 := by
    have h : b * (a * (a * b - 8 * a - 8 * b + 32)) = 0 := by
      have h1 : b * (a * (a * b - 8 * a - 8 * b + 32)) =
          a * b * (a * b - 8 * a - 8 * b + 32) := by ring
      rw [h1, hprod]
    rcases mul_eq_zero.mp h with hb_eq_zero | h_eq_zero
    · exact absurd hb_eq_zero hb0
    · exact h_eq_zero
  have hdiff : (a^2 - 8 * a) * b - 8 * a * (a - 4) =
      a * (a * b - 8 * a - 8 * b + 32) := by ring
  exact sub_eq_zero.mp (hdiff.trans hzero)

private theorem putnam_candidate_from_bounds_factor (a b c : ℤ) (ha : a > 0) (hab : a ≤ b)
    (hp : a^2 + b^2 = c^2) (harea : a * b = 4 * (a + b + c)) :
    (a - 8) * (b - 8) = 32 := by
  have hb : b > 0 := by linarith
  have h4c : 4 * c = a * b - 4 * a - 4 * b := by linarith [harea]
  have hsq : (a * b - 4 * a - 4 * b) ^ 2 = 16 * (a ^ 2 + b ^ 2) := by
    rw [← h4c, hp]
    ring
  have hprod : a * b * (a * b - 8 * a - 8 * b + 32) = 0 := by
    have h : (a * b - 4 * a - 4 * b) ^ 2 - 16 * (a ^ 2 + b ^ 2) =
        a * b * (a * b - 8 * a - 8 * b + 32) := by ring
    rw [hsq] at h
    rw [sub_self] at h
    exact h.symm
  have hab0 : a * b ≠ 0 := by
    have ha0 : a ≠ 0 := by linarith
    have hb0 : b ≠ 0 := by linarith
    exact mul_ne_zero ha0 hb0
  obtain hz | hbr := mul_eq_zero.mp hprod
  · exfalso
    exact hab0 hz
  · calc (a - 8) * (b - 8)
      = a * b - 8 * a - 8 * b + 64 := by ring
    _ = (a * b - 8 * a - 8 * b + 32) + 32 := by ring
    _ = 0 + 32 := by rw [hbr]
    _ = 32 := by ring

theorem putnam_candidate_from_bounds (a b c : ℤ) (ha : a > 0) (hab : a ≤ b) (hc : c > 0)
    (hp : a^2 + b^2 = c^2) (harea : a * b = 4 * (a + b + c))
    (h9 : 9 ≤ a) (h16 : a < 16) :
    (a, b, c) = (9, 40, 41) ∨ (a, b, c) = (10, 24, 26) ∨ (a, b, c) = (12, 16, 20) := by
  have hfac : (a - 8) * (b - 8) = 32 :=
    putnam_candidate_from_bounds_factor a b c ha hab hp harea
  interval_cases a
  · -- a = 9
    have hb : b = 40 := by
      norm_num at hfac
      omega
    subst hb
    have hc' : c = 41 := by
      norm_num at harea
      omega
    subst hc'
    left
    rfl
  · -- a = 10
    have hb : b = 24 := by
      norm_num at hfac
      omega
    subst hb
    have hc' : c = 26 := by
      norm_num at harea
      omega
    subst hc'
    right
    left
    rfl
  · -- a = 11
    exfalso
    norm_num at hfac
    omega
  · -- a = 12
    have hb : b = 16 := by
      norm_num at hfac
      omega
    subst hb
    have hc' : c = 20 := by
      norm_num at harea
      omega
    subst hc'
    right
    right
    rfl
  · -- a = 13
    exfalso
    norm_num at hfac
    omega
  · -- a = 14
    exfalso
    norm_num at hfac
    omega
  · -- a = 15
    exfalso
    norm_num at hfac
    omega

open EuclideanGeometry Topology Filter Complex

open EuclideanGeometry Topology Filter Complex

open EuclideanGeometry Topology Filter Complex

open EuclideanGeometry Topology Filter Complex

theorem putnam_candidates_in_set :
    {(9, 40, 41), (10, 24, 26), (12, 16, 20)} ⊆
      {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧
        a * b / (2 : ℚ) = 2 * (a + b + c)} := by
  intro x hx
  rcases x with ⟨a, b, c⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hx
  rcases hx with (h | h | h)
  · -- Case (a, b, c) = (9, 40, 41)
    rw [h]
    refine Set.mem_setOf.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    exact (putnam_rat_eq_iff 9 40 41).mpr (by norm_num)
  · -- Case (a, b, c) = (10, 24, 26)
    rw [h]
    refine Set.mem_setOf.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    exact (putnam_rat_eq_iff 10 24 26).mpr (by norm_num)
  · -- Case (a, b, c) = (12, 16, 20)
    rw [h]
    refine Set.mem_setOf.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    exact (putnam_rat_eq_iff 12 16 20).mpr (by norm_num)

/--
Prove that there are exactly three right triangles (up to orientation and translation) with integer side lengths and area equal to twice their perimeter.
-/
theorem putnam_1965_b3
: {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a*b/(2 : ℚ) = 2*(a + b + c)}.ncard = 3 := by
  have hsubset : {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ a ≤ b ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a*b/(2 : ℚ) = 2*(a + b + c)} ⊆ {(9, 40, 41), (10, 24, 26), (12, 16, 20)} := by
    rintro ⟨a, b, c⟩ ⟨ha, hab, hc, hp, hq⟩
    have harea := (putnam_rat_eq_iff a b c).mp hq
    have hb : b > 0 := by linarith
    obtain ⟨h9, h16⟩ := putnam_bounds a b c ha hab hc hp harea
    exact putnam_candidate_from_bounds a b c ha hab hc hp harea h9 h16
  have hsupset := putnam_candidates_in_set
  have hset := le_antisymm hsubset hsupset
  rw [hset]
  refine Set.ncard_eq_three.mpr ⟨(9, 40, 41), (10, 24, 26), (12, 16, 20), ?_, ?_, ?_, rfl⟩
  · decide
  · decide
  · decide

#print axioms putnam_1965_b3
