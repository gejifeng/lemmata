import Mathlib
open Nat


open Nat

open Nat

lemma sum_Icc_one_eq_sum_range {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    (∑ j ∈ Finset.Icc 1 n, f j) = ∑ i ∈ Finset.range n, f (i + 1) := by
  have him : (Finset.range n).image (fun i => i + 1) = Finset.Icc 1 n := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, hn⟩
      refine ⟨x - 1, ?_, ?_⟩
      · omega
      · omega
  rw [← him, Finset.sum_image (fun _ _ h => by simpa using h)]

lemma int_modEq_of_nat_modEq {n : ℕ} (hn : 0 < n) {a b : ℕ} (h : a ≡ b [MOD n]) :
    (a : ℤ) ≡ (b : ℤ) [ZMOD n] := by
  rw [Int.modEq_iff_dvd, Nat.modEq_iff_dvd] at *
  exact h

lemma int_modEq_sum {α : Type*} [DecidableEq α] (s : Finset α) {f g : α → ℤ} (n : ℤ)
    (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ (∑ x ∈ s, g x) [ZMOD n] := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/--
Prove that for $m = 5 \pmod 6$,
\[
\binom{m}{2} - \binom{m}{5} + \binom{m}{8} - \binom{m}{11} + ... - \binom{m}{m-6} + \binom{m}{m-3} \neq 0.
\]
-/
theorem putnam_1983_a4
(k m : ℕ)
(S : ℤ)
(kpos : k > 0)
(hm : m = 6 * k - 1)
(hS : S = ∑ j ∈ Finset.Icc 1 (2 * k - 1), (-1 : ℤ) ^ (j + 1) * choose m (3 * j - 1))
: (S ≠ 0) := by
  subst hm
  rw [hS]
  set n := 2 * k - 1 with hn
  have hk1 : k ≥ 1 := by omega
  have hn1 : n ≥ 1 := by omega

  rw [sum_Icc_one_eq_sum_range]
  have h_simp : ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1 + 1) * ↑((6 * k - 1).choose (3 * (i + 1) - 1))
      = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑((6 * k - 1).choose (3 * i + 2)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hidx : 3 * (i + 1) - 1 = 3 * i + 2 := by omega
    rw [hidx, pow_add]
    ring_nf
    <;> simp
  rw [h_simp]

  have h_lucas : ∀ i ∈ Finset.range n,
      ((6 * k - 1).choose (3 * i + 2) : ℤ) ≡ ((2 * k - 1).choose i : ℤ) [ZMOD 3] := by
    intro i hi
    have hmem : i < n := Finset.mem_range.mp hi
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 3) (n := 6 * k - 1) (k := 3 * i + 2)
    have hlow : (6 * k - 1) % 3 = 2 := by omega
    have hrlow : (3 * i + 2) % 3 = 2 := by omega
    have hhigh : (6 * k - 1) / 3 = n := by
      have : n = 2 * k - 1 := rfl
      omega
    have hrhigh : (3 * i + 2) / 3 = i := by omega
    rw [hlow, hrlow, hhigh, hrhigh] at h
    have h22 : (2 : ℕ).choose 2 = 1 := by decide
    rw [h22, one_mul] at h
    exact int_modEq_of_nat_modEq (by decide) h

  have h_term_cong : ∀ i ∈ Finset.range n,
      (-1 : ℤ) ^ i * ↑((6 * k - 1).choose (3 * i + 2)) ≡
      (-1 : ℤ) ^ i * ↑((2 * k - 1).choose i) [ZMOD 3] := by
    intro i hi
    exact (h_lucas i hi).mul_left _

  have h_sum_cong : (∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑((6 * k - 1).choose (3 * i + 2))) ≡
      (∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑((2 * k - 1).choose i)) [ZMOD 3] := by
    apply int_modEq_sum
    intro i hi
    exact h_term_cong i hi

  have h_full : (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ↑(n.choose i)) = 0 := by
    rw [Int.alternating_sum_range_choose]
    have hne : n ≠ 0 := by omega
    simp [hne]

  have h_split : (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ↑(n.choose i)) =
      (∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑(n.choose i)) + (-1 : ℤ) ^ n * ↑(n.choose n) := by
    rw [Finset.sum_range_succ]

  have h_last : (-1 : ℤ) ^ n * ↑(n.choose n) = -1 := by
    have hnn : n.choose n = 1 := Nat.choose_self n
    rw [hnn]
    have hn_form : n = 2 * (k - 1) + 1 := by
      have : n = 2 * k - 1 := rfl
      omega
    rw [hn_form, pow_add, pow_mul]
    norm_num

  have h_target : (∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑(n.choose i)) = 1 := by
    rw [h_split] at h_full
    rw [h_last] at h_full
    linarith

  have h_sum_mod : (∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ↑((6 * k - 1).choose (3 * i + 2))) ≡ 1 [ZMOD 3] := by
    rw [h_target] at h_sum_cong
    exact h_sum_cong

  intro hzero
  rw [hzero] at h_sum_mod
  rw [Int.modEq_iff_dvd] at h_sum_mod
  norm_num at h_sum_mod

#print axioms putnam_1983_a4
