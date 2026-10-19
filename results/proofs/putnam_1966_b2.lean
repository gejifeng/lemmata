import Mathlib


/-
Informal proof sketch.

Let T_n = {n, n+1, ..., n+9}.  We claim that among these ten integers there is
one which is coprime to 210 = 2·3·5·7.  Indeed, in any block of ten consecutive
integers there are five odd integers, forming an arithmetic progression
a, a+2, a+4, a+6, a+8.  Looking modulo 3, 5 and 7, the step 2 is invertible, so
among these five terms at most two are divisible by 3, exactly one is divisible
by 5, and at most one is divisible by 7.  Hence at most four of them are
divisible by one of 3,5,7, so one of them is coprime to 105; being odd, it is
coprime to 210.  (Equivalently, this can be checked on the finitely many
residue classes modulo 210.)

Choose k ∈ T_n with gcd(k,210)=1.  If m ∈ T_n and m ≠ k, then 0 < |m-k| ≤ 9.
Any common prime divisor p of m and k would divide m-k, hence p ≤ 9, so
p ∈ {2,3,5,7}; but k is coprime to 210, contradiction.  Therefore gcd(m,k)=1,
i.e. k is relatively prime to every other element of T_n.
-/

/-
Informal proof sketch.

Let T_n = {n, n+1, ..., n+9}.  We claim that among these ten integers there is
one which is coprime to 210 = 2·3·5·7.  Indeed, in any block of ten consecutive
integers there are five odd integers, forming an arithmetic progression
a, a+2, a+4, a+6, a+8.  Looking modulo 3, 5 and 7, the step 2 is invertible, so
among these five terms at most two are divisible by 3, exactly one is divisible
by 5, and at most one is divisible by 7.  Hence at most four of them are
divisible by one of 3,5,7, so one of them is coprime to 105; being odd, it is
coprime to 210.  (Equivalently, this can be checked on the finitely many
residue classes modulo 210.)

Choose k ∈ T_n with gcd(k,210)=1.  If m ∈ T_n and m ≠ k, then 0 < |m-k| ≤ 9.
Any common prime divisor p of m and k would divide m-k, hence p ≤ 9, so
p ∈ {2,3,5,7}; but k is coprime to 210, contradiction.  Therefore gcd(m,k)=1,
i.e. k is relatively prime to every other element of T_n.
-/

theorem mem_S_iff
    (S : ℤ → Set ℤ)
    (hS : S = fun n : ℤ => {n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7, n + 8, n + 9})
    (n x : ℤ) :
    x ∈ S n ↔ ∃ i ∈ Finset.range 10, x = n + (i : ℤ) := by
  rw [hS]
  have key :
      (∃ i ∈ Finset.range 10, x = n + (i : ℤ)) ↔
        (x = n ∨ x = n + 1 ∨ x = n + 2 ∨ x = n + 3 ∨ x = n + 4 ∨
         x = n + 5 ∨ x = n + 6 ∨ x = n + 7 ∨ x = n + 8 ∨ x = n + 9) := by
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : (i : ℤ) < 10 := by
        simpa using hi
      have hi'' : 0 ≤ (i : ℤ) := by
        have : (0 : ℕ) ≤ i := Nat.zero_le i
        exact_mod_cast this
      interval_cases (i : ℤ) <;> simp_all
    · rintro (h|h|h|h|h|h|h|h|h|h)
      · exact ⟨0, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨1, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨2, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨3, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨4, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨5, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨6, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨7, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨8, Finset.mem_range.mpr (by decide), by simpa using h⟩
      · exact ⟨9, Finset.mem_range.mpr (by decide), by simpa using h⟩
  rw [key]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-
Informal proof sketch.

Let T_n = {n, n+1, ..., n+9}.  We claim that among these ten integers there is
one which is coprime to 210 = 2·3·5·7.  Indeed, in any block of ten consecutive
integers there are five odd integers, forming an arithmetic progression
a, a+2, a+4, a+6, a+8.  Looking modulo 3, 5 and 7, the step 2 is invertible, so
among these five terms at most two are divisible by 3, exactly one is divisible
by 5, and at most one is divisible by 7.  Hence at most four of them are
divisible by one of 3,5,7, so one of them is coprime to 105; being odd, it is
coprime to 210.  (Equivalently, this can be checked on the finitely many
residue classes modulo 210.)

Choose k ∈ T_n with gcd(k,210)=1.  If m ∈ T_n and m ≠ k, then 0 < |m-k| ≤ 9.
Any common prime divisor p of m and k would divide m-k, hence p ≤ 9, so
p ∈ {2,3,5,7}; but k is coprime to 210, contradiction.  Therefore gcd(m,k)=1,
i.e. k is relatively prime to every other element of T_n.
-/

private lemma isCoprime_of_gcd_eq_one (a b : ℤ) (h : Int.gcd a b = 1) : IsCoprime a b := by
  have h1 : a * Int.gcdA a b + b * Int.gcdB a b = 1 := by
    rw [← Int.gcd_eq_gcd_ab a b]
    exact_mod_cast h
  refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
  have h2 : Int.gcdA a b * a + Int.gcdB a b * b = a * Int.gcdA a b + b * Int.gcdB a b := by ring
  rw [h2]
  exact h1

private lemma isCoprime_add_mul_right (a b c : ℤ) (h : IsCoprime a b) :
    IsCoprime (a + c * b) b := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x, y - c * x, ?_⟩
  calc x * (a + c * b) + (y - c * x) * b
      = x * a + x * c * b + (y * b - c * x * b) := by ring
    _ = x * a + y * b := by ring
    _ = 1 := hxy

private lemma h_exists_coprime_mod :
    ∀ r ∈ Finset.range 210, ∃ i ∈ Finset.range 10,
      Int.gcd ((r : ℤ) + (i : ℤ)) 210 = 1 := by
  classical
  intro r hr
  have hr' : r < 210 := Finset.mem_range.mp hr
  interval_cases r <;> decide

theorem exists_in_block_coprime_210 (n : ℤ) :
    ∃ i ∈ Finset.range 10, IsCoprime (n + (i : ℤ)) 210 := by
  have hne : (210 : ℤ) ≠ 0 := by norm_num
  have hpos : (0 : ℤ) < 210 := by norm_num
  have hr0 : 0 ≤ n % 210 := Int.emod_nonneg n hne
  have hrlt : n % 210 < 210 := Int.emod_lt_of_pos n hpos
  let rNat : ℕ := (n % 210).toNat
  have hrc : (rNat : ℤ) = n % 210 := Int.toNat_of_nonneg hr0
  have hrLt : rNat < 210 := by
    have : (rNat : ℤ) < 210 := by
      rw [hrc]
      exact_mod_cast hrlt
    exact_mod_cast this
  obtain ⟨i, hi, hgcd⟩ := h_exists_coprime_mod rNat (Finset.mem_range.mpr hrLt)
  have hcop : IsCoprime ((rNat : ℤ) + (i : ℤ)) 210 :=
    isCoprime_of_gcd_eq_one _ _ hgcd
  let q : ℤ := n / 210
  have hdiv : n = q * 210 + (rNat : ℤ) := by
    have h := Int.ediv_add_emod n 210
    rw [← hrc] at h
    ring_nf at h ⊢
    omega
  have h1 : n + (i : ℤ) = ((rNat : ℤ) + (i : ℤ)) + q * 210 := by
    rw [hdiv]
    ring
  refine ⟨i, hi, ?_⟩
  rw [h1]
  exact isCoprime_add_mul_right ((rNat : ℤ) + (i : ℤ)) 210 q hcop

/-
Informal proof sketch.

Let T_n = {n, n+1, ..., n+9}.  We claim that among these ten integers there is
one which is coprime to 210 = 2·3·5·7.  Indeed, in any block of ten consecutive
integers there are five odd integers, forming an arithmetic progression
a, a+2, a+4, a+6, a+8.  Looking modulo 3, 5 and 7, the step 2 is invertible, so
among these five terms at most two are divisible by 3, exactly one is divisible
by 5, and at most one is divisible by 7.  Hence at most four of them are
divisible by one of 3,5,7, so one of them is coprime to 105; being odd, it is
coprime to 210.  (Equivalently, this can be checked on the finitely many
residue classes modulo 210.)

Choose k ∈ T_n with gcd(k,210)=1.  If m ∈ T_n and m ≠ k, then 0 < |m-k| ≤ 9.
Any common prime divisor p of m and k would divide m-k, hence p ≤ 9, so
p ∈ {2,3,5,7}; but k is coprime to 210, contradiction.  Therefore gcd(m,k)=1,
i.e. k is relatively prime to every other element of T_n.
-/

lemma prime_le_nine_dvd_210 {p : ℕ} (hp : Nat.Prime p) (h : p ≤ 9) : p ∣ 210 := by
  have h2 : 2 ≤ p := hp.two_le
  have : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> revert hp <;> decide
  rcases this with rfl | rfl | rfl | rfl <;> norm_num

lemma eq_one_of_int_dvd_one {p : ℕ} (h : (p : ℤ) ∣ 1) : p = 1 := by
  obtain ⟨c, hc⟩ := h
  have hc' : (p : ℤ) * c = 1 := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hp_ne_zero : (p : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc'
    norm_num at hc'
  have hp_pos : 0 < (p : ℤ) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hc_ne_zero : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hc'
    norm_num at hc'
  have habs : (p : ℤ) * (c.natAbs : ℤ) = 1 := by
    have h1 := congr_arg (fun x : ℤ => |x|) hc'
    simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p), abs_one] at h1
    have h2 : (c.natAbs : ℤ) = |c| := by
      rcases le_total 0 c with hcn | hcn
      · rw [abs_of_nonneg hcn, Int.natAbs_of_nonneg hcn]
      · rw [abs_of_nonpos hcn, ← Int.natAbs_neg, Int.natAbs_of_nonneg (by linarith)]
    rw [← h2] at h1
    exact h1
  have hle : (p : ℤ) ≤ 1 := by
    have h1 : (1 : ℤ) ≤ (c.natAbs : ℤ) := by
      have : 0 < c.natAbs := Int.natAbs_pos.mpr hc_ne_zero
      exact_mod_cast Nat.succ_le_of_lt this
    have : (p : ℤ) ≤ (p : ℤ) * (c.natAbs : ℤ) := by
      simpa using mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [habs] at this
    exact this
  have hp1 : 1 ≤ p := by
    have : p ≠ 0 := by
      intro h0
      rw [h0] at hp_ne_zero
      simp at hp_ne_zero
    exact Nat.pos_iff_ne_zero.mpr this
  exact_mod_cast (by omega)

theorem coprime_if_coprime_210_and_close (k m : ℤ) (hk : IsCoprime k 210)
    (h : |(m - k : ℤ)| ≤ 9) (hne : k ≠ m) : IsCoprime m k := by
  set t := m - k with ht_def
  have ht : t ≠ 0 := by
    intro h0
    exact hne (sub_eq_zero.mp h0).symm
  -- First show IsCoprime k t.
  have hk_t : IsCoprime k t := by
    have h_gcd : Int.gcd k t = 1 := by
      by_contra hne1
      have h_dvd_t : ((Int.gcd k t : ℕ) : ℤ) ∣ t := Int.gcd_dvd_right k t
      have h0 : Int.gcd k t ≠ 0 := by
        intro hz
        have h_dvd_t' : ((0 : ℕ) : ℤ) ∣ t := by simpa [hz] using h_dvd_t
        rcases h_dvd_t' with ⟨c, hc⟩
        simp at hc
        exact ht hc
      have hpos : 0 < Int.gcd k t := Nat.pos_of_ne_zero h0
      have hg2 : 1 < Int.gcd k t := by omega
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (by omega : Int.gcd k t ≠ 1)
      -- p divides both k and t in ℤ.
      have hp_gcd : (p : ℤ) ∣ (Int.gcd k t : ℤ) := by
        obtain ⟨c, hc⟩ := hpg
        exact ⟨c, by simp [hc]⟩
      have hp_k : (p : ℤ) ∣ k := hp_gcd.trans (Int.gcd_dvd_left k t)
      have hp_t : (p : ℤ) ∣ t := hp_gcd.trans (Int.gcd_dvd_right k t)
      -- Convert divisibility to natAbs.
      have hp_nat_t : p ∣ t.natAbs := by
        exact Int.ofNat_dvd_left.mp hp_t
      -- Bound p by |t| ≤ 9.
      have h_abs_le : t.natAbs ≤ 9 := by
        first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
      have hp_le : p ≤ t.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr ht) hp_nat_t
      have hp9 : p ≤ 9 := by omega
      -- p is a prime ≤ 9, so p ∣ 210.
      have hp210 : (p : ℤ) ∣ (210 : ℤ) := by
        exact_mod_cast prime_le_nine_dvd_210 hp hp9
      -- p divides k and 210, contradicting IsCoprime k 210.
      obtain ⟨u, v, huv⟩ := hk
      have h_p1 : (p : ℤ) ∣ 1 := by
        have h1 : (p : ℤ) ∣ u * k := dvd_mul_of_dvd_right hp_k u
        have h2 : (p : ℤ) ∣ v * (210 : ℤ) := dvd_mul_of_dvd_right hp210 v
        have h3 : (p : ℤ) ∣ u * k + v * (210 : ℤ) := dvd_add h1 h2
        rwa [huv] at h3
      have h_p_eq_1_nat : p = 1 := eq_one_of_int_dvd_one h_p1
      have : p ≥ 2 := hp.two_le
      omega
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h_gcd
  -- Now show IsCoprime m k. Note m = k + t.
  have h_m_eq : k + t = m := by
    dsimp [t]
    ring
  have : IsCoprime (k + t) k := by
    obtain ⟨u, v, huv⟩ := hk_t
    refine ⟨v, u - v, ?_⟩
    calc (v : ℤ) * (k + t) + (u - v) * k
        = v * k + v * t + u * k - v * k := by ring
      _ = u * k + v * t := by ring
      _ = 1 := huv
  rw [h_m_eq] at this
  exact this

/--
Prove that, for any ten consecutive integers, at least one is relatively prime to all of the others.
-/
theorem putnam_1966_b2
(S : ℤ → Set ℤ)
(hS : S = fun n : ℤ => {n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7, n + 8, n + 9})
: ∀ n : ℤ, n > 0 → (∃ k ∈ S n, ∀ m ∈ S n, k ≠ m → IsCoprime m k) := by
  intro n hn
  obtain ⟨i, hi, hgi⟩ := exists_in_block_coprime_210 n
  refine ⟨n + (i : ℤ), ?_, fun m hm hne => ?_⟩
  · rw [mem_S_iff S hS n (n + (i : ℤ))]
    exact ⟨i, hi, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := (mem_S_iff S hS n m).mp hm
    apply coprime_if_coprime_210_and_close (k := n + (i : ℤ)) (m := n + (j : ℤ)) hgi
    · have hsub : (n + (j : ℤ)) - (n + (i : ℤ)) = (j : ℤ) - (i : ℤ) := by ring
      rw [hsub]
      have hj10 : (j : ℤ) ≤ 9 := by
        have hj9 : j ≤ 9 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact_mod_cast hj9
      have hi10 : (i : ℤ) ≤ 9 := by
        have hi9 : i ≤ 9 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact_mod_cast hi9
      have hj0 : 0 ≤ (j : ℤ) := by positivity
      have hi0 : 0 ≤ (i : ℤ) := by positivity
      apply abs_le.mpr
      constructor <;> linarith
    · exact hne

#print axioms putnam_1966_b2
