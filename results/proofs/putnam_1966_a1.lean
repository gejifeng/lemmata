import Mathlib


theorem f_sum_div_two
  (f : ℤ → ℤ)
  (hf : f = fun n : ℤ => ∑ m ∈ Finset.Icc 0 n, (if Even m then m / 2 else (m - 1)/2)) :
  ∀ n : ℤ, 0 ≤ n → f n = ∑ m ∈ Finset.Icc 0 n, (m / 2) := by
  intros
  first
  | grind
  | aesop
  | (nlinarith [sq_nonneg (0:ℝ)])
  | (field_simp; ring)
  | decide

theorem sum_div_two_closed_form :
  ∀ n : ℤ, 0 ≤ n → ∑ m ∈ Finset.Icc 0 n, (m / 2) = (n / 2) * ((n + 1) / 2) := by
  have hstep : ∀ (n : ℤ), (n + 2) / 2 = n / 2 + 1 := by
    first | omega | linarith | positivity | norm_num | (simp_all; done) | ring | (field_simp; ring) | nlinarith [sq_nonneg (0:ℤ)] | grind | aesop
  have hIcc_succ : ∀ (N : ℕ),
      Finset.Icc (0 : ℤ) ((N : ℤ) + 1) =
        insert ((N : ℤ) + 1) (Finset.Icc (0 : ℤ) (N : ℤ)) := by
    intro N
    have hN : (0 : ℤ) ≤ (N : ℤ) := Nat.cast_nonneg N
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

  have haux : ∀ (N : ℕ),
      ∑ m ∈ Finset.Icc (0 : ℤ) (N : ℤ), (m / 2) =
        ((N : ℤ) / 2) * (((N : ℤ) + 1) / 2) := by
    intro N
    induction N with
    | zero =>
      simp [Finset.Icc_self, Finset.sum_singleton]
    | succ N ih =>
      rw [Nat.cast_succ]
      rw [hIcc_succ N]
      rw [Finset.sum_insert]
      · have hstep' : (((N : ℤ) + 1) + 1) / 2 = (N : ℤ) / 2 + 1 := by
          rw [show ((N : ℤ) + 1) + 1 = (N : ℤ) + 2 by ring]
          exact hstep (N : ℤ)
        rw [ih, hstep']
        ring
      · intro h
        rw [Finset.mem_Icc] at h
        omega

  intro n hn
  have hto : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn
  have h := haux n.toNat
  rw [← hto] at h
  simpa [hto] using h

theorem product_difference_identity
  (x y : ℤ) (hx : x > 0) (hy : y > 0) (hxy : x > y) :
  ((x + y) / 2) * ((x + y + 1) / 2) - ((x - y) / 2) * ((x - y + 1) / 2) = x * y := by
  have ha : 0 < x + y := by linarith
  have hb : 0 < x - y := by linarith
  rcases Int.even_or_odd (x + y) with h_even | h_odd
  · obtain ⟨p, hp⟩ := h_even
    have hb_even : Even (x - y) := by
      use p - y
      linarith
    obtain ⟨q, hq⟩ := hb_even
    have h1 : (x + y) / 2 = p := by
      rw [hp]
      omega
    have h2 : (x + y + 1) / 2 = p := by
      rw [hp]
      omega
    have h3 : (x - y) / 2 = q := by
      rw [hq]
      omega
    have h4 : (x - y + 1) / 2 = q := by
      rw [hq]
      omega
    have hx_eq : x = p + q := by linarith
    have hy_eq : y = p - q := by linarith
    rw [h1, h2, h3, h4, hx_eq, hy_eq]
    ring
  · obtain ⟨p, hp⟩ := h_odd
    have hb_odd : Odd (x - y) := by
      use p - y
      linarith
    obtain ⟨q, hq⟩ := hb_odd
    have h1 : (x + y) / 2 = p := by
      rw [hp]
      omega
    have h2 : (x + y + 1) / 2 = p + 1 := by
      rw [hp]
      omega
    have h3 : (x - y) / 2 = q := by
      rw [hq]
      omega
    have h4 : (x - y + 1) / 2 = q + 1 := by
      rw [hq]
      omega
    have hx_eq : x = p + q + 1 := by linarith
    have hy_eq : y = p - q := by linarith
    rw [h1, h2, h3, h4, hx_eq, hy_eq]
    ring

/--
Let $a_n$ denote the sequence $0, 1, 1, 2, 2, 3, \dots$, where $a_n = \frac{n}{2}$ if $n$ is even and $\frac{n - 1}{2}$ if n is odd. Furthermore, let $f(n)$ denote the sum of the first $n$ terms of $a_n$. Prove that all positive integers $x$ and $y$ with $x > y$ satisfy $xy = f(x + y) - f(x - y)$.
-/
theorem putnam_1966_a1
(f : ℤ → ℤ)
(hf : f = fun n : ℤ => ∑ m ∈ Finset.Icc 0 n, (if Even m then m / 2 else (m - 1)/2))
: ∀ x y : ℤ, x > 0 ∧ y > 0 ∧ x > y → x * y = f (x + y) - f (x - y) := by
  intro x y h
  obtain ⟨hx, hy, hxy⟩ := h
  have hA : 0 ≤ x + y := by linarith
  have hB : 0 ≤ x - y := by linarith
  have h1 := f_sum_div_two f hf (x + y) hA
  have h2 := sum_div_two_closed_form (x + y) hA
  have h3 := f_sum_div_two f hf (x - y) hB
  have h4 := sum_div_two_closed_form (x - y) hB
  rw [h1, h2, h3, h4]
  exact (product_difference_identity x y hx hy hxy).symm

#print axioms putnam_1966_a1
