import Mathlib
open Topology Filter


/-
Informal proof sketch.

1. From f(2)=2 and multiplicativity at (1,2), we get f(1)=1.
2. From f(1)=1 and strict monotonicity on {1,2,...}, we get f(n) >= n for all n>=1.
3. We first prove f(3)=3. Suppose a=f(3)>=4. Using multiplicativity at coprime pairs:
   f(6)=f(2)f(3)=2a, f(12)=f(3)f(4)=a f(4), f(14)=f(2)f(7)=2 f(7).
   Strict monotonicity gives f(4)>=a+1, f(7)>=2a+1, and f(13)>=f(12)+1.
   Hence f(12)>=a(a+1), f(13)>=a(a+1)+1, while f(14)>=4a+2.
   Since f(13)<f(14), we get a^2+a+1 < 4a+2, impossible for a>=4. Thus f(3)<=3, and by step 2 f(3)=3.
4. Now prove by induction on N that f(k)=k for every 1<=k<=N.
   The base and the cases K=1,2,3 are already known.
   For K=N+1>=4, take M=N(N-1). Since gcd(N,N-1)=1, multiplicativity gives
   f(M)=f(N)f(N-1)=N(N-1)=M, using the induction hypothesis.
   Also M>=K. By strict monotonicity, f(K)+(M-K)<=f(M)=M, so f(K)<=K.
   Together with f(K)>=K, we conclude f(K)=K.
5. Therefore f(n)=n for every positive integer n.
-/

theorem isRelPrime_consecutive : ∀ n : ℕ, n ≥ 2 → IsRelPrime n (n - 1) := by
  intro n hn
  have hle : 1 ≤ n := by omega
  have hc : Nat.Coprime n (n - 1) := by
    exact (Nat.coprime_self_sub_right hle).mpr (Nat.coprime_one_right n)
  exact Nat.coprime_iff_isRelPrime.mp hc

theorem putnam_f1_eq
    (f : ℕ → ℕ)
    (hf2 : f 2 = 2)
    (hfmn : ∀ m n, m > 0 → n > 0 → IsRelPrime m n → f (m * n) = f m * f n) :
    f 1 = 1 := by
  have h := hfmn 2 1 (by omega) (by omega) (isRelPrime_consecutive 2 (by omega))
  rw [Nat.mul_one, hf2] at h
  have h2 : 2 * f 1 = 2 * 1 := by
    rw [h.symm, Nat.mul_one]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0 : ℕ) < 2) h2

open Topology Filter


/-
Informal proof sketch.

1. From f(2)=2 and multiplicativity at (1,2), we get f(1)=1.
2. From f(1)=1 and strict monotonicity on {1,2,...}, we get f(n) >= n for all n>=1.
3. We first prove f(3)=3. Suppose a=f(3)>=4. Using multiplicativity at coprime pairs:
   f(6)=f(2)f(3)=2a, f(12)=f(3)f(4)=a f(4), f(14)=f(2)f(7)=2 f(7).
   Strict monotonicity gives f(4)>=a+1, f(7)>=2a+1, and f(13)>=f(12)+1.
   Hence f(12)>=a(a+1), f(13)>=a(a+1)+1, while f(14)>=4a+2.
   Since f(13)<f(14), we get a^2+a+1 < 4a+2, impossible for a>=4. Thus f(3)<=3, and by step 2 f(3)=3.
4. Now prove by induction on N that f(k)=k for every 1<=k<=N.
   The base and the cases K=1,2,3 are already known.
   For K=N+1>=4, take M=N(N-1). Since gcd(N,N-1)=1, multiplicativity gives
   f(M)=f(N)f(N-1)=N(N-1)=M, using the induction hypothesis.
   Also M>=K. By strict monotonicity, f(K)+(M-K)<=f(M)=M, so f(K)<=K.
   Together with f(K)>=K, we conclude f(K)=K.
5. Therefore f(n)=n for every positive integer n.
-/

theorem putnam_f3_eq
    (f : ℕ → ℕ)
    (hfpos : ∀ n, f n > 0)
    (hfinc : StrictMonoOn f (Set.Ici 1))
    (hf2 : f 2 = 2)
    (hfmn : ∀ m n, m > 0 → n > 0 → IsRelPrime m n → f (m * n) = f m * f n) :
    f 3 = 3 := by
  have h32 : f 2 < f 3 := hfinc (by simp) (by simp) (by omega)
  rw [hf2] at h32
  have ha3 : 3 ≤ f 3 := by omega

  by_contra hne
  push_neg at hne
  have ha4 : 4 ≤ f 3 := by omega
  set a := f 3 with ha
  set d := f 7 with hd

  have hrp27 : IsRelPrime 2 7 := by
    rw [← Nat.coprime_iff_isRelPrime]
    decide
  have hrp38 : IsRelPrime 3 8 := by
    rw [← Nat.coprime_iff_isRelPrime]
    decide
  have hrp213 : IsRelPrime 2 13 := by
    rw [← Nat.coprime_iff_isRelPrime]
    decide

  have hf14 : f 14 = 2 * f 7 := by
    have : 14 = 2 * 7 := by norm_num
    rw [this, hfmn 2 7 (by omega) (by omega) hrp27]
    rw [hf2]

  have hf24 : f 24 = f 3 * f 8 := by
    have : 24 = 3 * 8 := by norm_num
    rw [this, hfmn 3 8 (by omega) (by omega) hrp38]

  have hf26 : f 26 = f 2 * f 13 := by
    have : 26 = 2 * 13 := by norm_num
    rw [this, hfmn 2 13 (by omega) (by omega) hrp213]

  have h78 : f 7 < f 8 := hfinc (by simp) (by simp) (by omega)
  have h13_14 : f 13 < f 14 := hfinc (by simp) (by simp) (by omega)
  have h24_26 : f 24 < f 26 := hfinc (by simp) (by simp) (by omega)

  rw [hf24, hf26] at h24_26
  rw [hf14] at h13_14

  have h8ge : d + 1 ≤ f 8 := by
    have h : f 7 < f 8 := h78
    rw [← hd] at h
    exact Nat.succ_le_of_lt h

  have hmul : 2 * f 13 < 4 * d := by
    have h1 : f 13 < 2 * d := by
      rw [← hd] at h13_14
      exact h13_14
    have h2 : 2 * f 13 < 2 * (2 * d) := Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
    have h_eq : 2 * (2 * d) = 4 * d := by ring
    rw [h_eq] at h2
    exact h2

  have h_lower : a * (d + 1) ≤ a * f 8 := Nat.mul_le_mul_left a h8ge

  have h24' : a * f 8 < 2 * f 13 := by
    rw [← ha, hf2] at h24_26
    exact h24_26

  have h_chain : a * (d + 1) < 4 * d := calc
    a * (d + 1) ≤ a * f 8 := h_lower
    _ < 2 * f 13 := h24'
    _ < 4 * d := hmul

  have ha4a : 4 ≤ a := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have h4 : 4 * (d + 1) ≤ a * (d + 1) := Nat.mul_le_mul_right (d + 1) ha4a
  have h5 : 4 * (d + 1) < 4 * d := lt_of_le_of_lt h4 h_chain
  have h6 : 4 * d + 4 < 4 * d := by
    have : 4 * (d + 1) = 4 * d + 4 := by ring
    omega
  omega

open Topology Filter


/-
Informal proof sketch.

1. From f(2)=2 and multiplicativity at (1,2), we get f(1)=1.
2. From f(1)=1 and strict monotonicity on {1,2,...}, we get f(n) >= n for all n>=1.
3. We first prove f(3)=3. Suppose a=f(3)>=4. Using multiplicativity at coprime pairs:
   f(6)=f(2)f(3)=2a, f(12)=f(3)f(4)=a f(4), f(14)=f(2)f(7)=2 f(7).
   Strict monotonicity gives f(4)>=a+1, f(7)>=2a+1, and f(13)>=f(12)+1.
   Hence f(12)>=a(a+1), f(13)>=a(a+1)+1, while f(14)>=4a+2.
   Since f(13)<f(14), we get a^2+a+1 < 4a+2, impossible for a>=4. Thus f(3)<=3, and by step 2 f(3)=3.
4. Now prove by induction on N that f(k)=k for every 1<=k<=N.
   The base and the cases K=1,2,3 are already known.
   For K=N+1>=4, take M=N(N-1). Since gcd(N,N-1)=1, multiplicativity gives
   f(M)=f(N)f(N-1)=N(N-1)=M, using the induction hypothesis.
   Also M>=K. By strict monotonicity, f(K)+(M-K)<=f(M)=M, so f(K)<=K.
   Together with f(K)>=K, we conclude f(K)=K.
5. Therefore f(n)=n for every positive integer n.
-/

theorem putnam_ge_self
    (f : ℕ → ℕ)
    (hfinc : StrictMonoOn f (Set.Ici 1))
    (h1 : f 1 = 1) :
    ∀ n : ℕ, 1 ≤ n → n ≤ f n := by
  intro n
  induction n with
  | zero =>
      intro h
      omega
  | succ n ih =>
      intro h
      cases n with
      | zero =>
          rw [h1]
      | succ m =>
          have him := ih (by omega)
          have hx : (m + 1 : ℕ) ∈ Set.Ici 1 := Set.mem_Ici.mpr (by omega)
          have hy : (m + 2 : ℕ) ∈ Set.Ici 1 := Set.mem_Ici.mpr (by omega)
          have hlt : (m + 1 : ℕ) < m + 2 := by omega
          have hf := hfinc hx hy hlt
          exact Nat.le_trans (Nat.succ_le_succ him) (Nat.succ_le_of_lt hf)

open Topology Filter


/-
Informal proof sketch.

1. From f(2)=2 and multiplicativity at (1,2), we get f(1)=1.
2. From f(1)=1 and strict monotonicity on {1,2,...}, we get f(n) >= n for all n>=1.
3. We first prove f(3)=3. Suppose a=f(3)>=4. Using multiplicativity at coprime pairs:
   f(6)=f(2)f(3)=2a, f(12)=f(3)f(4)=a f(4), f(14)=f(2)f(7)=2 f(7).
   Strict monotonicity gives f(4)>=a+1, f(7)>=2a+1, and f(13)>=f(12)+1.
   Hence f(12)>=a(a+1), f(13)>=a(a+1)+1, while f(14)>=4a+2.
   Since f(13)<f(14), we get a^2+a+1 < 4a+2, impossible for a>=4. Thus f(3)<=3, and by step 2 f(3)=3.
4. Now prove by induction on N that f(k)=k for every 1<=k<=N.
   The base and the cases K=1,2,3 are already known.
   For K=N+1>=4, take M=N(N-1). Since gcd(N,N-1)=1, multiplicativity gives
   f(M)=f(N)f(N-1)=N(N-1)=M, using the induction hypothesis.
   Also M>=K. By strict monotonicity, f(K)+(M-K)<=f(M)=M, so f(K)<=K.
   Together with f(K)>=K, we conclude f(K)=K.
5. Therefore f(n)=n for every positive integer n.
-/

open Topology Filter


/-
Informal proof sketch.

1. From f(2)=2 and multiplicativity at (1,2), we get f(1)=1.
2. From f(1)=1 and strict monotonicity on {1,2,...}, we get f(n) >= n for all n>=1.
3. We first prove f(3)=3. Suppose a=f(3)>=4. Using multiplicativity at coprime pairs:
   f(6)=f(2)f(3)=2a, f(12)=f(3)f(4)=a f(4), f(14)=f(2)f(7)=2 f(7).
   Strict monotonicity gives f(4)>=a+1, f(7)>=2a+1, and f(13)>=f(12)+1.
   Hence f(12)>=a(a+1), f(13)>=a(a+1)+1, while f(14)>=4a+2.
   Since f(13)<f(14), we get a^2+a+1 < 4a+2, impossible for a>=4. Thus f(3)<=3, and by step 2 f(3)=3.
4. Now prove by induction on N that f(k)=k for every 1<=k<=N.
   The base and the cases K=1,2,3 are already known.
   For K=N+1>=4, take M=N(N-1). Since gcd(N,N-1)=1, multiplicativity gives
   f(M)=f(N)f(N-1)=N(N-1)=M, using the induction hypothesis.
   Also M>=K. By strict monotonicity, f(K)+(M-K)<=f(M)=M, so f(K)<=K.
   Together with f(K)>=K, we conclude f(K)=K.
5. Therefore f(n)=n for every positive integer n.
-/

theorem putnam_upper
    (f : ℕ → ℕ)
    (hfinc : StrictMonoOn f (Set.Ici 1)) :
    ∀ a b : ℕ, 1 ≤ a → a ≤ b → f b = b → f a ≤ a := by
  intro a b ha hab hfb
  have key : ∀ k : ℕ, f a + k ≤ f (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : a + k ∈ Set.Ici 1 := by
          rw [Set.mem_Ici]
          exact Nat.le_trans ha (Nat.le_add_right a k)
        have h2 : a + k + 1 ∈ Set.Ici 1 := by
          rw [Set.mem_Ici]
          exact Nat.le_trans (Nat.le_trans ha (Nat.le_add_right a k)) (Nat.le_add_right (a + k) 1)
        have hstep := hfinc h1 h2 (Nat.lt_succ_self (a + k))
        calc
          f a + (k + 1) = f a + k + 1 := by rw [Nat.add_assoc]
          _ ≤ f (a + k) + 1 := Nat.add_le_add_right ih 1
          _ ≤ f (a + k + 1) := Nat.succ_le_of_lt hstep
  have hab_eq : a + (b - a) = b := Nat.add_sub_of_le hab
  have h := key (b - a)
  rw [hab_eq, hfb] at h
  have h' : f a + (b - a) ≤ b := h
  have : f a + (b - a) ≤ a + (b - a) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  exact Nat.le_of_add_le_add_right this

/--
Let $\{f(n)\}$ be a strictly increasing sequence of positive integers such that $f(2)=2$ and $f(mn)=f(m)f(n)$ for every relatively prime pair of positive integers $m$ and $n$ (the greatest common divisor of $m$ and $n$ is equal to $1$). Prove that $f(n)=n$ for every positive integer $n$.
-/
theorem putnam_1963_a2
(f : ℕ → ℕ)
(hfpos : ∀ n, f n > 0)
(hfinc : StrictMonoOn f (Set.Ici 1))
(hf2 : f 2 = 2)
(hfmn : ∀ m n, m > 0 → n > 0 → IsRelPrime m n → f (m * n) = f m * f n)
: ∀ n > 0, f n = n := by
  intro n hn
  have h1 : f 1 = 1 := putnam_f1_eq f hf2 hfmn
  have h3 : f 3 = 3 := putnam_f3_eq f hfpos hfinc hf2 hfmn
  have hge : ∀ k : ℕ, 1 ≤ k → k ≤ f k := putnam_ge_self f hfinc h1
  have key : ∀ N : ℕ, ∀ k : ℕ, k ≤ N → k > 0 → f k = k := by
    intro N
    induction N with
    | zero =>
      intro k hk hk0
      omega
    | succ N ih =>
      intro k hk hk0
      rcases Nat.lt_or_ge k N with hltN | hgeN
      · exact ih k (Nat.le_of_lt hltN) hk0
      · rcases Nat.eq_or_lt_of_le hgeN with hkeq | hgtN
        · subst hkeq
          exact ih N (Nat.le_refl N) hk0
        · have hK : k = N + 1 := by omega
          subst hK
          by_cases hK1 : N + 1 = 1
          · rw [hK1]
            exact h1
          by_cases hK2 : N + 1 = 2
          · rw [hK2]
            exact hf2
          by_cases hK3 : N + 1 = 3
          · rw [hK3]
            exact h3
          have hKge4 : N + 1 ≥ 4 := by omega
          have hNge3 : N ≥ 3 := by omega
          have hNpos : N > 0 := by omega
          have hN1pos : N - 1 > 0 := by omega
          have fN : f N = N := ih N (Nat.le_refl N) hNpos
          have fN1 : f (N - 1) = N - 1 := ih (N - 1) (Nat.sub_le N 1) hN1pos
          have hrp : IsRelPrime N (N - 1) := isRelPrime_consecutive N (by omega)
          have hM : f (N * (N - 1)) = N * (N - 1) := by
            have h := hfmn N (N - 1) hNpos hN1pos hrp
            rw [fN, fN1] at h
            exact h
          have hMge : N + 1 ≤ N * (N - 1) := by
            have hN1ge2 : 2 ≤ N - 1 := by omega
            have hN1_2 : N + 1 ≤ N * 2 := by
              have : N * 2 = N + N := by ring
              rw [this]
              omega
            exact Nat.le_trans hN1_2 (Nat.mul_le_mul_left N hN1ge2)
          have hle : f (N + 1) ≤ N + 1 :=
            putnam_upper f hfinc (N + 1) (N * (N - 1)) (by omega) hMge hM
          have hgeK : N + 1 ≤ f (N + 1) := hge (N + 1) (by omega)
          exact Nat.le_antisymm hle hgeK
  exact key n n (Nat.le_refl n) hn

#print axioms putnam_1963_a2
