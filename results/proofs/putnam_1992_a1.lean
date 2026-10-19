import Mathlib
open Topology Filter


/--
Prove that $f(n) = 1-n$ is the only integer-valued function defined on the integers that satisfies the following conditions.
\begin{itemize}
\item[(i)] $f(f(n)) = n$, for all integers $n$;
\item[(ii)] $f(f(n+2)+2) = n$ for all integers $n$;
\item[(iii)] $f(0) = 1$.
\end{itemize}
-/
theorem putnam_1992_a1
  (f : ℤ → ℤ) :
  (f = fun n ↦ 1 - n) ↔
  (∀ n : ℤ, f (f n) = n) ∧ (∀ n : ℤ, f (f (n + 2) + 2) = n) ∧ (f 0 = 1) := by
  constructor
  · intro h
    subst h
    refine ⟨fun n => by show (1 : ℤ) - ((1 : ℤ) - n) = n; ring,
              fun n => by show (1 : ℤ) - (((1 : ℤ) - (n + 2)) + 2) = n; ring,
              by show (1 : ℤ) - 0 = 1; norm_num⟩
  · rintro ⟨h1, h2, h3⟩
    have f1 : f 1 = 0 := by simpa [h3] using h1 0
    have rec_step : ∀ n : ℤ, f (n + 2) = f n - 2 := by
      intro n
      have hf := congr_arg f (h2 n)
      rw [h1 (f (n + 2) + 2)] at hf
      rw [← hf]
      ring
    have pos : ∀ k : ℕ, f (k : ℤ) = 1 - (k : ℤ) := by
      have Q : ∀ n : ℕ, (f (n : ℤ) = 1 - (n : ℤ)) ∧ (f ((n + 1 : ℕ) : ℤ) = 1 - ((n + 1 : ℕ) : ℤ)) := by
        intro n
        induction n with
        | zero =>
          constructor
          · simpa using h3
          · simpa using f1
        | succ n ih =>
          obtain ⟨hn, hn1⟩ := ih
          refine ⟨hn1, ?_⟩
          have hcast : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by norm_cast
          rw [hcast, rec_step (n : ℤ), hn]
          ring
      intro k
      exact (Q k).1
    funext n
    by_cases hn : 0 ≤ n
    · have h := pos n.toNat
      rw [Int.toNat_of_nonneg hn] at h
      exact h
    · have hm : 0 ≤ 1 - n := by omega
      have h := pos (1 - n).toNat
      rw [Int.toNat_of_nonneg hm] at h
      have hsub : (1 : ℤ) - (1 - n) = n := by ring
      rw [hsub] at h
      have hinv := h1 (1 - n)
      rw [h] at hinv
      exact hinv

#print axioms putnam_1992_a1
