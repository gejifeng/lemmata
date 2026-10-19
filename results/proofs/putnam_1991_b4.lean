import Mathlib
open Filter Topology


open Filter Topology

open Filter Topology

open Filter Topology

namespace Putnam1991B4

lemma add_choose_range (m n k : ℕ) :
    (m + n).choose k = ∑ i ∈ Finset.range (k + 1), m.choose i * n.choose (k - i) := by
  have h := Nat.add_choose_eq m n k
  have hEq : Finset.antidiagonal k = Finset.image (fun i => (i, k - i)) (Finset.range (k + 1)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_antidiagonal, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hab
      refine ⟨a, by omega, ?_⟩
      ext <;> omega
    · rintro ⟨i, hi, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst_vars
      omega
  rw [hEq, Finset.sum_image] at h
  · exact h
  · intro i _ j _ hij
    simp only [Prod.mk.injEq] at hij
    exact hij.1

lemma modEq_mul_of_dvd {p a b : ℕ} (hp : 1 < p) (h1 : p ∣ a) (h2 : b ≡ 1 [MOD p]) :
    a * b ≡ a [MOD p ^ 2] := by
  obtain ⟨c, rfl⟩ := h1
  have hmod : b % p = 1 % p := h2
  have h1lt : 1 % p = 1 := Nat.mod_eq_of_lt hp
  rw [h1lt] at hmod
  have hdiv := Nat.div_add_mod b p
  rw [Nat.add_comm] at hdiv
  rw [hmod] at hdiv
  have hb : ∃ q, b = p * q + 1 := ⟨b / p, by omega⟩
  obtain ⟨q, hq⟩ := hb
  rw [hq]
  have hgoal : (p * c) * (p * q + 1) = p * c + p ^ 2 * (c * q) := by ring
  rw [hgoal]
  have h0 : (p ^ 2 * (c * q) : ℕ) ≡ 0 [MOD p ^ 2] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨c * q, by ring⟩
  exact h0.add_left (p * c)

lemma choose_p_add_j_modEq_one {p j : ℕ} (pp : Nat.Prime p) (hj : j < p) :
    (p + j).choose j ≡ 1 [MOD p] := by
  rw [add_choose_range]
  have hsplit : (∑ i ∈ Finset.range (j + 1), p.choose i * j.choose (j - i)) =
      1 + ∑ i ∈ Finset.Ico 1 (j + 1), p.choose i * j.choose (j - i) := by
    have h1 : Finset.range (j + 1) = {0} ∪ Finset.Ico 1 (j + 1) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_union]
    · rw [Finset.sum_singleton]
      simp
    · rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [Finset.mem_singleton, Finset.mem_Ico] at hy1 hy2
      omega
  rw [hsplit]
  have h_mid : (∑ i ∈ Finset.Ico 1 (j + 1), p.choose i * j.choose (j - i)) ≡
      ∑ i ∈ Finset.Ico 1 (j + 1), 0 [MOD p] := by
    apply Nat.ModEq.sum
    intro i hi
    have hi1 : 1 ≤ i := by simp only [Finset.mem_Ico] at hi; exact hi.1
    have hi2 : i < p := by
      have : i ≤ j := by simp only [Finset.mem_Ico] at hi; omega
      omega
    have hd : p ∣ p.choose i := Nat.Prime.dvd_choose_self pp (by omega) hi2
    have : p ∣ p.choose i * j.choose (j - i) := hd.mul_right _
    exact Nat.modEq_zero_iff_dvd.mpr this
  have hsum0 : (∑ i ∈ Finset.Ico 1 (j + 1), 0) = 0 := by simp
  rw [hsum0] at h_mid
  have h1 : (1 : ℕ) ≡ 1 [MOD p] := Nat.ModEq.refl _
  exact h1.add h_mid

lemma sum_range_choose_p {p : ℕ} (hp : 0 < p) :
    (∑ j ∈ Finset.range p, p.choose j) = 2 ^ p - 1 := by
  have hfull := Nat.sum_range_choose p
  have hsplit : (∑ j ∈ Finset.range (p + 1), p.choose j) =
      (∑ j ∈ Finset.range p, p.choose j) + p.choose p := by
    rw [Finset.sum_range_succ]
  rw [hsplit] at hfull
  have := Nat.choose_self p
  rw [this] at hfull
  omega

lemma modEq_sq_zero_of_dvd {n a : ℕ} (h : n ∣ a) : a ^ 2 ≡ 0 [MOD n ^ 2] := by
  obtain ⟨m, rfl⟩ := h
  rw [mul_pow]
  rw [Nat.modEq_zero_iff_dvd]
  exact ⟨m ^ 2, by ring⟩

lemma choose_mul_choose_modEq {p j : ℕ} (pp : Nat.Prime p) (hj : j < p) :
    (p.choose j) * ((p + j).choose j) ≡ p.choose j [MOD p ^ 2] := by
  by_cases hj0 : j = 0
  · subst hj0
    simp [Nat.ModEq]
  · have hpos : 0 < j := Nat.pos_of_ne_zero hj0
    have h1 : p ∣ p.choose j := Nat.Prime.dvd_choose_self pp (by omega) hj
    have h2 := choose_p_add_j_modEq_one pp hj
    exact modEq_mul_of_dvd (Nat.Prime.one_lt pp) h1 h2

lemma choose_two_p_eq_sum_sq {p : ℕ} :
    (2 * p).choose p = ∑ k ∈ Finset.range (p + 1), (p.choose k) ^ 2 := by
  have : 2 * p = p + p := by ring
  rw [this, add_choose_range p p p]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ p := by
    simp only [Finset.mem_range] at hk
    omega
  rw [Nat.choose_symm hk', pow_two]

lemma choose_two_mul_prime_modEq_two {p : ℕ} (pp : Nat.Prime p) (po : Odd p) :
    (2 * p).choose p ≡ 2 [MOD p ^ 2] := by
  rw [choose_two_p_eq_sum_sq]
  have hp : 0 < p := Nat.Prime.pos pp
  have h_split : (∑ k ∈ Finset.range (p + 1), (p.choose k) ^ 2) =
      (p.choose 0) ^ 2 + (∑ k ∈ Finset.Ico 1 p, (p.choose k) ^ 2) + (p.choose p) ^ 2 := by
    have h1 : Finset.range (p + 1) = {0} ∪ Finset.Ico 1 p ∪ {p} := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    rw [h1]
    have hd1 : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 p) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [Finset.mem_singleton, Finset.mem_Ico] at hy1 hy2
      omega
    have hd2 : Disjoint ({0} ∪ Finset.Ico 1 p) ({p} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at hy1 hy2
      rcases hy1 with (rfl | hy1) <;>
      (try { simp_all }) <;>
      (try { omega }) <;>
      (try { cases hy2 <;> simp_all })
    rw [Finset.sum_union hd2, Finset.sum_union hd1]
    · simp [Finset.sum_singleton]
  rw [h_split]
  have h0 : (p.choose 0) ^ 2 = 1 := by simp
  have hpv : (p.choose p) ^ 2 = 1 := by simp
  rw [h0, hpv]
  have h_mid : (∑ k ∈ Finset.Ico 1 p, (p.choose k) ^ 2) ≡ 0 [MOD p ^ 2] := by
    have h_mid' : (∑ k ∈ Finset.Ico 1 p, (p.choose k) ^ 2) ≡ ∑ k ∈ Finset.Ico 1 p, 0 [MOD p ^ 2] := by
      apply Nat.ModEq.sum
      intro k hk
      have hk1 : 1 ≤ k := by simp only [Finset.mem_Ico] at hk; exact hk.1
      have hk2 : k < p := by simp only [Finset.mem_Ico] at hk; exact hk.2
      have hdiv : p ∣ p.choose k := Nat.Prime.dvd_choose_self pp (by omega) hk2
      exact modEq_sq_zero_of_dvd hdiv
    have hsum0 : (∑ k ∈ Finset.Ico 1 p, 0) = 0 := by simp
    rw [hsum0] at h_mid'
    exact h_mid'
  have hmid : (1 + ∑ k ∈ Finset.Ico 1 p, (p.choose k) ^ 2) ≡ 1 + 0 [MOD p ^ 2] :=
    h_mid.add_left 1
  have : (1 + ∑ k ∈ Finset.Ico 1 p, (p.choose k) ^ 2) + 1 ≡ 2 [MOD p ^ 2] := by
    convert hmid.add_right 1 using 1 <;> omega
  simpa [Nat.add_assoc] using this

end Putnam1991B4

/--
Suppose $p$ is an odd prime. Prove that $\sum_{j=0}^p \binom{p}{j}\binom{p+j}{j} \equiv 2^p+1 \pmod{p^2}$.
-/
theorem putnam_1991_b4
(p : ℕ)
(podd : Odd p)
(pprime : Prime p)
: (∑ j : Fin (p + 1), (p.choose j) * ((p + j).choose j)) ≡ (2 ^ p + 1) [MOD (p ^ 2)] := by
  have pN : Nat.Prime p := by
    exact Prime.nat_prime pprime
  have hp : 0 < p := Nat.Prime.pos pN
  have h_conv' : (∑ j : Fin (p + 1), (p.choose j) * ((p + j).choose j)) =
      ∑ j ∈ Finset.range (p + 1), (p.choose j) * ((p + j).choose j) := by
    classical
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp [if_pos (by omega : (j : ℕ) ≤ p)]
  rw [h_conv']
  have h_split : (∑ j ∈ Finset.range (p + 1), (p.choose j) * ((p + j).choose j)) =
      (∑ j ∈ Finset.range p, (p.choose j) * ((p + j).choose j)) +
      (p.choose p) * ((p + p).choose p) := by
    rw [Finset.sum_range_succ]
  rw [h_split]
  have h_cong : (∑ j ∈ Finset.range p, (p.choose j) * ((p + j).choose j)) ≡
      (∑ j ∈ Finset.range p, p.choose j) [MOD p ^ 2] := by
    apply Nat.ModEq.sum
    intro j hj
    exact Putnam1991B4.choose_mul_choose_modEq pN (Finset.mem_range.mp hj)
  have h_sum_val : (∑ j ∈ Finset.range p, p.choose j) = 2 ^ p - 1 :=
    Putnam1991B4.sum_range_choose_p hp
  have h_cong2 : (∑ j ∈ Finset.range p, (p.choose j) * ((p + j).choose j)) ≡
      (2 ^ p - 1) [MOD p ^ 2] := by
    rw [← h_sum_val]
    exact h_cong
  have h_last : (p.choose p) * ((p + p).choose p) = (2 * p).choose p := by
    have : p + p = 2 * p := by ring
    rw [this, Nat.choose_self]
    simp
  have h_c2p : (2 * p).choose p ≡ 2 [MOD p ^ 2] :=
    Putnam1991B4.choose_two_mul_prime_modEq_two pN podd
  have h_last_cong : (p.choose p) * ((p + p).choose p) ≡ 2 [MOD p ^ 2] := by
    rw [h_last]; exact h_c2p
  have h_main : (∑ j ∈ Finset.range p, (p.choose j) * ((p + j).choose j)) +
      (p.choose p) * ((p + p).choose p) ≡ (2 ^ p - 1) + 2 [MOD p ^ 2] :=
    h_cong2.add h_last_cong
  have h_final : (2 ^ p - 1) + 2 = 2 ^ p + 1 := by
    have : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by omega)
    omega
  rw [h_final] at h_main
  exact h_main

#print axioms putnam_1991_b4
