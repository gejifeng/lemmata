import Mathlib


/--
Let $(x_n)_{n \geq 0}$ be a sequence of nonzero real numbers such that $x_n^2-x_{n-1}x_{n+1}=1$ for $n=1,2,3,\dots$. Prove there exists a real number $a$ such that $x_{n+1}=ax_n-x_{n-1}$ for all $n \geq 1$.
-/
theorem putnam_1993_a2
(x : ℕ → ℝ)
(xnonzero : ∀ n : ℕ, x n ≠ 0)
(hx : ∀ n ≥ 1, (x n) ^ 2 - x (n - 1) * x (n + 1) = 1)
: ∃ a : ℝ, ∀ n ≥ 1, x (n + 1) = a * x n - x (n - 1) := by
  let r : ℕ → ℝ := fun n => (x (n + 1) + x (n - 1)) / x n
  have r_step : ∀ n ≥ 1, r (n + 1) = r n := by
    intro n hn
    have h1 := hx n hn
    have h2 := hx (n + 1) (by omega)
    have h1' : x (n - 1) * x (n + 1) = x n ^ 2 - 1 := by linarith [h1]
    have h2' : x n * x (n + 2) = x (n + 1) ^ 2 - 1 := by
      have h2'' : x (n + 1) ^ 2 - x (n + 1 - 1) * x (n + 1 + 1) = 1 := h2
      have h2''' : x (n + 1 - 1) = x n := by
        have : n + 1 - 1 = n := by omega
        rw [this]
      have h2'''' : x (n + 1 + 1) = x (n + 2) := by
        have : n + 1 + 1 = n + 2 := by omega
        rw [this]
      rw [h2''', h2''''] at h2''
      linarith
    have key : (x (n + 2) + x n) * x n = (x (n + 1) + x (n - 1)) * x (n + 1) := by
      calc (x (n + 2) + x n) * x n
          = x n * x (n + 2) + x n ^ 2 := by ring
        _ = (x (n + 1) ^ 2 - 1) + x n ^ 2 := by rw [h2']
        _ = x (n + 1) ^ 2 + (x n ^ 2 - 1) := by ring
        _ = x (n + 1) ^ 2 + x (n - 1) * x (n + 1) := by rw [h1']
        _ = (x (n + 1) + x (n - 1)) * x (n + 1) := by ring
    show (x (n + 2) + x n) / x (n + 1) = (x (n + 1) + x (n - 1)) / x n
    rw [div_eq_div_iff (xnonzero (n + 1)) (xnonzero n)]
    exact key
  have hr : ∀ n : ℕ, n ≥ 1 → r n = r 1 := by
    intro n
    induction n with
    | zero =>
      intro h
      exact absurd h (by omega)
    | succ n ih =>
      intro h
      cases n with
      | zero => rfl
      | succ n =>
        have hstep := r_step (n + 1) (by omega)
        have hih := ih (by omega)
        exact hstep.trans hih
  use r 1
  intro n hn
  have hdiv := hr n hn
  change (x (n + 1) + x (n - 1)) / x n = r 1 at hdiv
  rw [div_eq_iff (xnonzero n)] at hdiv
  rw [← hdiv]
  ring

#print axioms putnam_1993_a2
