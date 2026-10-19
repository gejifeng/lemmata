import Mathlib
open Set Filter Topology


theorem helper_one_pos : (1 : ℤ) > 0 := by
  intros
  first
  | omega
  | linarith
  | positivity
  | norm_num
  | (simp_all; done)
  | ring

theorem helper_sub_one_pos (n : ℤ) (h : 2 ≤ n) : n - 1 > 0 := by
  intros
  first
  | omega
  | linarith
  | positivity
  | norm_num
  | (simp_all; done)
  | ring

theorem helper_composite_identity (a b : ℤ) :
    a * b = (a - 1) * (b - 1) + (a - 1) * 1 + (b - 1) * 1 + 1 := by
  intros
  first
  | omega
  | linarith
  | positivity
  | norm_num
  | (simp_all; done)
  | ring

/--
A \emph{composite} (positive integer) is a product $ab$ with $a$ and $b$ not necessarily distinct integers in $\{2,3,4,\dots\}$. Show that every composite is expressible as $xy+xz+yz+1$, with $x,y,z$ positive integers.
-/
theorem putnam_1988_b1
: ∀ a ≥ 2, ∀ b ≥ 2, ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a * b = x * y + x * z + y * z + 1 := by
  intro a ha b hb
  use a - 1, b - 1, 1
  exact ⟨helper_sub_one_pos a ha, helper_sub_one_pos b hb, helper_one_pos,
    helper_composite_identity a b⟩

#print axioms putnam_1988_b1
