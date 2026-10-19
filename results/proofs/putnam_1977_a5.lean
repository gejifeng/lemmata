import Mathlib
open RingHom Set Nat


open Nat

theorem mul_mod_eq_zero (p a : ℕ) (hp : p ≠ 0) : (p * a) % p = 0 := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

theorem mul_div_eq_of_pos (p a : ℕ) (hp : 0 < p) : (p * a) / p = a := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

theorem lucas_one_digit (p n k : ℕ) [Fact (Nat.Prime p)] :
    (Nat.choose n k ≡ Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) [MOD p]) := by
  intros
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

/--
Let $p$ be a prime and $m \geq n$ be non-negative integers. Show that $\binom{pm}{pn} = \binom{m}{n} \pmod p$, where $\binom{m}{n}$ is the binomial coefficient.
-/
theorem putnam_1977_a5
(p m n : ℕ)
(hp : Nat.Prime p)
(hmgen : m ≥ n)
: (choose (p * m) (p * n) ≡ choose m n [MOD p]) := by
  haveI : Fact p.Prime := Fact.mk hp
  have h0 := lucas_one_digit p (p * m) (p * n)
  have hmodm := mul_mod_eq_zero p m hp.ne_zero
  have hmodn := mul_mod_eq_zero p n hp.ne_zero
  have hdivm := mul_div_eq_of_pos p m hp.pos
  have hdivn := mul_div_eq_of_pos p n hp.pos
  rw [hmodm, hmodn, hdivm, hdivn] at h0
  rw [Nat.choose_self 0, one_mul] at h0
  exact h0

#print axioms putnam_1977_a5
