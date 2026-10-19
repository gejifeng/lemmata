import Mathlib
open Topology Filter


/-
Informal proof sketch:
For a given n, take r = n + 1 and x = 2r(r+1). Then x is a sum of two squares:
x = x^2 + 0^2. Also x + 1 = x^2 + 1^2. Finally, using the identity
(x - 1)^2 + (2r + 1)^2 = x^2 + 2, we get x + 2 as a sum of two squares.
Choosing r = n + 1 makes x^2 arbitrarily large, so x^2 > n.
-/

theorem putnam_2000_a2_growth (n : ℕ) :
    (n : ℤ) < ((2 * (n + 1) * (n + 2) : ℕ) : ℤ)^2 := by
  intros
  first
  | grind
  | aesop
  | (nlinarith [sq_nonneg (0:ℝ)])
  | (field_simp; ring)
  | decide

theorem putnam_2000_a2_identity (r : ℕ) (hr : 1 ≤ r) :
    ((((2 * r * (r + 1) : ℕ) - 1) : ℤ)^2 + ((2 * r + 1 : ℕ) : ℤ)^2 =
      ((2 * r * (r + 1) : ℕ) : ℤ)^2 + 2) := by
  intros
  first
  | grind
  | aesop
  | (nlinarith [sq_nonneg (0:ℝ)])
  | (field_simp; ring)
  | decide

/--
Prove that there exist infinitely many integers $n$ such that $n,n+1,n+2$ are each the sum of the squares of two integers.
-/
theorem putnam_2000_a2 :
  ∀ n : ℕ,
    ∃ N : ℤ,
      ∃ i : Fin 6 → ℕ,
        N > n ∧
        N = (i 0)^2 + (i 1)^2 ∧
        N + 1 = (i 2)^2 + (i 3)^2 ∧
        N + 2 = (i 4)^2 + (i 5)^2 := by
  intro n
  set r := n + 1 with r_def
  set x := 2 * r * (r + 1) with x_def
  have hr : 1 ≤ r := by omega
  have hgr : (n : ℤ) < (x : ℤ)^2 := by
    simpa [r_def, x_def] using putnam_2000_a2_growth n
  have hid : ((x - 1 : ℕ) : ℤ)^2 + ((2 * r + 1 : ℕ) : ℤ)^2 = (x : ℤ)^2 + 2 := by
    simpa [r_def, x_def] using putnam_2000_a2_identity r hr
  use (x : ℤ)^2
  let i : Fin 6 → ℕ := fun k =>
    if k.val = 0 then x
    else if k.val = 1 then 0
    else if k.val = 2 then x
    else if k.val = 3 then 1
    else if k.val = 4 then x - 1
    else if k.val = 5 then 2 * r + 1
    else 0
  use i
  refine ⟨by simpa using hgr, ?_, ?_, ?_⟩
  · have h0 : i 0 = x := by simp [i]
    have h1 : i 1 = 0 := by simp [i]
    rw [h0, h1]
    push_cast
    ring
  · have h2 : i 2 = x := by simp [i]
    have h3 : i 3 = 1 := by simp [i]
    rw [h2, h3]
    push_cast
    ring
  · have h4 : i 4 = x - 1 := by simp [i]
    have h5 : i 5 = 2 * r + 1 := by simp [i]
    rw [h4, h5]
    push_cast
    exact hid.symm

#print axioms putnam_2000_a2
