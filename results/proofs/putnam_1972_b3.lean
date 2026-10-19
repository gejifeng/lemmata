import Mathlib
open EuclideanGeometry Filter Topology Set MeasureTheory Metric


open EuclideanGeometry Filter Topology Set MeasureTheory Metric

theorem aba_to_square
  {G : Type*} [Group G]
  (A B : G)
  (h : A * B * A = B * A^2 * B)
  (hA : A^3 = 1) :
  A * B = (B * A^2) ^ 2 := by
  have hAA2 : A * A^2 = 1 := by
    calc
      A * A^2 = A ^ (2 + 1) := (pow_succ' A 2).symm
      _ = A ^ 3 := by rw [show (2 : ℕ) + 1 = 3 by norm_num]
      _ = 1 := hA
  symm
  calc
    (B * A^2) ^ 2 = (B * A^2) * (B * A^2) := by rw [pow_two]
    _ = ((B * A^2) * B) * A^2 := by rw [← mul_assoc]
    _ = (A * B * A) * A^2 := by rw [← h]
    _ = (A * B) * (A * A^2) := by rw [mul_assoc]
    _ = (A * B) * 1 := by rw [hAA2]
    _ = A * B := by rw [mul_one]

open EuclideanGeometry Filter Topology Set MeasureTheory Metric

open EuclideanGeometry Filter Topology Set MeasureTheory Metric

theorem commutes_with_square
  {G : Type*} [Group G]
  (A B : G)
  (h : A * B * A = B * A^2 * B)
  (hA : A^3 = 1) :
  A * B^2 = B^2 * A := by
  set C := B * A^2 with hC_def
  rw [hC_def] at h
  have two_add_one : (2 : ℕ) + 1 = 3 := rfl
  have hA2 : A^2 * A = 1 := by
    rw [← pow_succ, two_add_one, hA]
  have hAA2 : A * A^2 = 1 := by
    rw [pow_two, ← mul_assoc, ← pow_two, hA2]
  have hB : C * A = B := by
    show (B * A^2) * A = B
    rw [mul_assoc, hA2, mul_one]
  have hC2 : C^2 = A * B := by
    calc C^2 = (B * A^2)^2 := by rw [hC_def]
      _ = (B * A^2) * (B * A^2) := by rw [pow_two]
      _ = (B * A^2 * B) * A^2 := by simp [mul_assoc]
      _ = (A * B * A) * A^2 := by rw [← h]
      _ = A * B * (A * A^2) := by simp [mul_assoc]
      _ = A * B * 1 := by rw [hAA2]
      _ = A * B := by rw [mul_one]
  have hACA : A * C * A = C^2 := by
    calc A * C * A = A * (B * A^2) * A := by rw [hC_def]
      _ = A * B * (A^2 * A) := by simp [mul_assoc]
      _ = A * B * 1 := by rw [hA2]
      _ = A * B := by rw [mul_one]
      _ = C^2 := hC2.symm
  have hKey : A * C * A^2 = C^2 * A := by
    calc A * C * A^2 = A * C * (A * A) := by rw [pow_two]
      _ = (A * C * A) * A := by simp [mul_assoc]
      _ = C^2 * A := by rw [hACA]
  have hC3_left : C * C^2 = C^3 := by
    rw [pow_two, ← mul_assoc, ← pow_two, ← pow_succ, two_add_one]
  have hLeft : A * B^2 = C^3 * A := by
    rw [pow_two, hB.symm]
    calc A * ((C * A) * (C * A)) = (A * C * A) * (C * A) := by simp [mul_assoc]
      _ = C^2 * (C * A) := by rw [hACA]
      _ = (C^2 * C) * A := by simp [mul_assoc]
      _ = C^3 * A := by rw [← pow_succ, two_add_one]
  have hRight : B^2 * A = C^3 * A := by
    rw [pow_two, hB.symm]
    calc ((C * A) * (C * A)) * A = C * (A * C * A^2) := by
          rw [pow_two]
          simp [mul_assoc]
      _ = C * (C^2 * A) := by rw [hKey]
      _ = (C * C^2) * A := by simp [mul_assoc]
      _ = C^3 * A := by rw [hC3_left]
  rw [hLeft, hRight]

open EuclideanGeometry Filter Topology Set MeasureTheory Metric

theorem commute_of_odd_order
  {G : Type*} [Group G]
  (A B : G)
  (hcomm : A * B^2 = B^2 * A)
  (n : ℤ)
  (hn : n > 0)
  (hB : B ^ (2 * n - 1) = 1) :
  A * B = B * A := by
  -- First, establish that A commutes with B^2 (as an integer power).
  have hsq : A * (B * B) = (B * B) * A := by
    rw [← pow_two]
    exact hcomm
  have hc : Commute A (B ^ (2 : ℤ)) := by
    -- B ^ (2 : ℤ) = B * B
    have hz2 : B ^ (2 : ℤ) = B * B := by
      have h2 : (2 : ℤ) = 1 + 1 := by norm_num
      rw [h2, zpow_add, zpow_one]
    rw [hz2]
    exact hsq
  -- Now A commutes with (B^2)^n for any integer n.
  have hAB2n : Commute A (B ^ (2 * n)) := by
    have := hc.zpow_right n
    -- (B^(2:ℤ))^n = B^(2*n)
    have hmul : (B ^ (2 : ℤ)) ^ n = B ^ (2 * n) := (zpow_mul B (2 : ℤ) n).symm
    rw [hmul] at this
    exact this
  -- Show that B^(2*n) = B using the hypothesis hB.
  have hB2n : B ^ (2 * n) = B := by
    have hexp : (2 * n : ℤ) = (2 * n - 1) + 1 := by ring
    rw [hexp, zpow_add, hB, zpow_one, one_mul]
  -- Substitute back into the commutation relation.
  have hAB : Commute A B := by
    rw [← hB2n]
    exact hAB2n
  exact hAB

open EuclideanGeometry Filter Topology Set MeasureTheory Metric

open EuclideanGeometry Filter Topology Set MeasureTheory Metric

theorem one_of_commute_and_relation
  {G : Type*} [Group G]
  (A B : G)
  (h : A * B * A = B * A^2 * B)
  (hcomm : A * B = B * A) :
  B = 1 := by
  have hAB2 : A * B * A = A^2 * B := by
    rw [pow_two]
    calc
      A * B * A = A * (B * A) := mul_assoc A B A
      _ = A * (A * B) := by rw [hcomm.symm]
      _ = (A * A) * B := (mul_assoc A A B).symm
  have hBA2 : B * A^2 = A^2 * B := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hR : B * A^2 * B = A^2 * B^2 := by
    rw [hBA2, pow_two B, mul_assoc]
  have hEq : A^2 * B = A^2 * B^2 := by
    rw [← hAB2, h, hR]
  have hB : B = B^2 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  rw [pow_two] at hB
  have hB1 : B * 1 = B * B := by
    rw [mul_one]
    exact hB
  exact (mul_left_cancel hB1).symm

/--
Let $A$ and $B$ be two elements in a group such that $ABA = BA^2B$, $A^3 = 1$, and $B^{2n-1} = 1$ for some positive integer $n$. Prove that $B = 1$.
-/
theorem putnam_1972_b3
(G : Type*) [Group G]
(A B : G)
(hab : A * B * A = B * A^2 * B ∧ A^3 = 1 ∧ (∃ n : ℤ, n > 0 ∧ B^(2*n - 1) = 1))
: B = 1 := by
  rcases hab with ⟨hABA, hA3, n, hn, hB⟩
  have hcomm2 : A * B^2 = B^2 * A := commutes_with_square A B hABA hA3
  have hcomm : A * B = B * A := commute_of_odd_order A B hcomm2 n hn hB
  exact one_of_commute_and_relation A B hABA hcomm

#print axioms putnam_1972_b3
