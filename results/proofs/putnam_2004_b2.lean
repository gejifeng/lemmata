import Mathlib
open Nat Topology Filter


open Nat Topology Filter

open Nat Topology Filter

open Nat Topology Filter

open Nat Topology Filter

/--
Let $m$ and $n$ be positive integers. Show that $\frac{(m+n)!}{(m+n)^{m+n}}<\frac{m!}{m^m}\frac{n!}{n^n}$.
-/
theorem putnam_2004_b2
(m n : ℕ)
(mnpos : m > 0 ∧ n > 0)
: ((m + n)! / ((m + n) ^ (m + n) : ℚ)) < (((m)! / (m ^ m : ℚ)) * ((n)! / (n ^ n : ℚ))) := by
  obtain ⟨hm, hn⟩ := mnpos
  let N := m + n
  have hN : 0 < N := by omega
  have hle : m ≤ N := Nat.le_add_right m n
  have hsub : N - m = n := Nat.add_sub_cancel_left m n
  let c : ℚ := (Nat.choose N m : ℚ) * (m : ℚ)^m * (n : ℚ)^n
  let f : ℕ → ℚ := fun i => if i = m then c else 0
  let g : ℕ → ℚ := fun i => (Nat.choose N i : ℚ) * (m : ℚ)^i * (n : ℚ)^(N - i)
  have hm_mem : m ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]; omega
  have h0_mem : (0 : ℕ) ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]; omega
  have hsum : ∑ i ∈ Finset.range (N + 1), g i = (N : ℚ)^N := by
    have hbase : (N : ℚ) = (m : ℚ) + (n : ℚ) := by simp [N]
    rw [hbase, add_pow]
    apply Finset.sum_congr rfl
    intro i _
    simp only [g]
    ring
  have hfg : ∀ i ∈ Finset.range (N + 1), f i ≤ g i := by
    intro i hi
    by_cases h : i = m
    · subst h
      simp only [f, g, c, hsub]
      exact le_refl _
    · simp only [f, if_neg h]
      positivity
  have h0lt : f 0 < g 0 := by
    have h0ne : (0 : ℕ) ≠ m := by omega
    simp only [f, if_neg h0ne]
    have hg0 : g 0 = (n : ℚ)^N := by
      simp only [g, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one, Nat.sub_zero]
    rw [hg0]
    positivity
  have hlt : ∑ i ∈ Finset.range (N + 1), f i < ∑ i ∈ Finset.range (N + 1), g i := by
    refine Finset.sum_lt_sum hfg ⟨0, h0_mem, h0lt⟩
  have hsumf : ∑ i ∈ Finset.range (N + 1), f i = c := by
    have : ∑ i ∈ Finset.range (N + 1), f i = f m := by
      first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
    rw [this]
    simp only [f, if_pos rfl]
  have hchoosepow : (Nat.choose N m : ℚ) * (m : ℚ)^m * (n : ℚ)^n < (N : ℚ)^N := by
    have hlt' := hlt
    rw [hsumf, hsum] at hlt'
    exact hlt'
  have hfac : (Nat.choose N m : ℚ) * (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ) = (Nat.factorial N : ℚ) := by
    rw [← hsub]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  have hmul : (Nat.factorial N : ℚ) * (m : ℚ)^m * (n : ℚ)^n < (N : ℚ)^N * (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ) := by
    have hpos : 0 < (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ) := by positivity
    have h := mul_lt_mul_of_pos_right hchoosepow hpos
    calc
      (Nat.factorial N : ℚ) * (m : ℚ)^m * (n : ℚ)^n
          = ((Nat.choose N m : ℚ) * (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ)) * ((m : ℚ)^m * (n : ℚ)^n) := by
            rw [← hfac]; ring
      _ = ((Nat.choose N m : ℚ) * (m : ℚ)^m * (n : ℚ)^n) * ((Nat.factorial m : ℚ) * (Nat.factorial n : ℚ)) := by ring
      _ < (N : ℚ)^N * ((Nat.factorial m : ℚ) * (Nat.factorial n : ℚ)) := h
      _ = (N : ℚ)^N * (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ) := by ring
  have hdenL : 0 < (N : ℚ)^N := by positivity
  have hdenR : 0 < (m : ℚ)^m * (n : ℚ)^n := by positivity
  have hgoal : (Nat.factorial N : ℚ) / (N : ℚ)^N < (Nat.factorial m : ℚ) * (Nat.factorial n : ℚ) / ((m : ℚ)^m * (n : ℚ)^n) := by
    rw [div_lt_div_iff₀ hdenL hdenR]
    convert hmul using 1 <;> ring
  simpa [N, _root_.div_mul_div_comm] using hgoal

#print axioms putnam_2004_b2
