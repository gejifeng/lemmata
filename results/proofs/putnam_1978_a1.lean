import Mathlib


/-
Informal proof sketch.

Write S = {3j + 1 | j ∈ ℤ, 0 ≤ j ≤ 33}.  Thus S has 34 elements indexed by
the integers 0,1,...,33.  Given T ⊆ S with |T| = 20, let A be the set of
indices j ∈ {0,...,33} such that 3j+1 ∈ T.  Then |A| = |T| = 20.

Two elements 3i+1 and 3j+1 of T sum to 104 iff 3(i+j)+2 = 104, i.e. iff
i+j = 34.  Partition {0,...,33} into the 17 pairs {0,34}, {1,33}, ...,
{16,18}, together with the singleton {17}; equivalently, there are 18
"blocks" such that two distinct indices in the same block sum to 34.
If A contained no two distinct indices summing to 34, then A would contain
at most one index from each of these 18 blocks, so |A| ≤ 18.  But |A| = 20,
contradiction.  Hence there exist distinct i,j ∈ A with i+j = 34, and then
m = 3i+1 and n = 3j+1 are distinct elements of T with m+n = 104.
-/

-- Combinatorial core: a subset of {0,...,33} of size 20 contains two distinct

-- indices summing to 34.

/-
Informal proof sketch.

Write S = {3j + 1 | j ∈ ℤ, 0 ≤ j ≤ 33}.  Thus S has 34 elements indexed by
the integers 0,1,...,33.  Given T ⊆ S with |T| = 20, let A be the set of
indices j ∈ {0,...,33} such that 3j+1 ∈ T.  Then |A| = |T| = 20.

Two elements 3i+1 and 3j+1 of T sum to 104 iff 3(i+j)+2 = 104, i.e. iff
i+j = 34.  Partition {0,...,33} into the 17 pairs {0,34}, {1,33}, ...,
{16,18}, together with the singleton {17}; equivalently, there are 18
"blocks" such that two distinct indices in the same block sum to 34.
If A contained no two distinct indices summing to 34, then A would contain
at most one index from each of these 18 blocks, so |A| ≤ 18.  But |A| = 20,
contradiction.  Hence there exist distinct i,j ∈ A with i+j = 34, and then
m = 3i+1 and n = 3j+1 are distinct elements of T with m+n = 104.
-/

-- Combinatorial core: a subset of {0,...,33} of size 20 contains two distinct

-- indices summing to 34.

/-
Informal proof sketch.

Write S = {3j + 1 | j ∈ ℤ, 0 ≤ j ≤ 33}.  Thus S has 34 elements indexed by
the integers 0,1,...,33.  Given T ⊆ S with |T| = 20, let A be the set of
indices j ∈ {0,...,33} such that 3j+1 ∈ T.  Then |A| = |T| = 20.

Two elements 3i+1 and 3j+1 of T sum to 104 iff 3(i+j)+2 = 104, i.e. iff
i+j = 34.  Partition {0,...,33} into the 17 pairs {0,34}, {1,33}, ...,
{16,18}, together with the singleton {17}; equivalently, there are 18
"blocks" such that two distinct indices in the same block sum to 34.
If A contained no two distinct indices summing to 34, then A would contain
at most one index from each of these 18 blocks, so |A| ≤ 18.  But |A| = 20,
contradiction.  Hence there exist distinct i,j ∈ A with i+j = 34, and then
m = 3i+1 and n = 3j+1 are distinct elements of T with m+n = 104.
-/

-- Combinatorial core: a subset of {0,...,33} of size 20 contains two distinct

-- indices summing to 34.

theorem index_pair_lemma (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (0 : ℤ) 33)
    (hcard : A.card = 20) :
    ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ i + j = 34 := by
  by_contra h
  have hno : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ 34 := by
    intro x hx y hy hxy hsum
    exact h ⟨x, hx, y, hy, hxy, hsum⟩
  let g : ℤ → ℕ := fun x => (min x (34 - x)).toNat
  have hrange : ∀ x ∈ A, g x < 18 := by
    intro x hx
    have hxI := hA hx
    have hx0 : (0 : ℤ) ≤ x := (Finset.mem_Icc.mp hxI).1
    have hx33 : x ≤ 33 := (Finset.mem_Icc.mp hxI).2
    have hmn : 0 ≤ min x (34 - x) := le_min hx0 (by omega)
    have hmx : min x (34 - x) ≤ 17 := by
      rcases lt_or_ge x 18 with hlt | hge
      · exact le_trans (min_le_left _ _) (by omega)
      · exact le_trans (min_le_right _ _) (by omega)
    have hge : (g x : ℤ) ≤ 17 := by
      change (((min x (34 - x)).toNat : ℕ) : ℤ) ≤ 17
      rw [Int.toNat_of_nonneg hmn]
      exact hmx
    have : (g x : ℤ) < 18 := by omega
    exact_mod_cast this
  have hI : Set.InjOn g (A : Set ℤ) := by
    intro x hx y hy hxy
    have hxI := hA hx
    have hyI := hA hy
    have hx0 : (0 : ℤ) ≤ x := (Finset.mem_Icc.mp hxI).1
    have hx33 : x ≤ 33 := (Finset.mem_Icc.mp hxI).2
    have hy0 : (0 : ℤ) ≤ y := (Finset.mem_Icc.mp hyI).1
    have hy33 : y ≤ 33 := (Finset.mem_Icc.mp hyI).2
    have hmn : 0 ≤ min x (34 - x) := le_min hx0 (by omega)
    have hmy : 0 ≤ min y (34 - y) := le_min hy0 (by omega)
    have hkx : (g x : ℤ) = min x (34 - x) := by
      change (((min x (34 - x)).toNat : ℕ) : ℤ) = _
      exact Int.toNat_of_nonneg hmn
    have hky : (g y : ℤ) = min y (34 - y) := by
      change (((min y (34 - y)).toNat : ℕ) : ℤ) = _
      exact Int.toNat_of_nonneg hmy
    have hmin : min x (34 - x) = min y (34 - y) := by
      rw [← hkx, ← hky, hxy]
    have hkg : g x = g y := hxy
    by_cases hk17 : g x = 17
    · have hx17 : x = 17 := by
        have h1 : (g x : ℤ) = 17 := by exact_mod_cast hk17
        have h2 : (g x : ℤ) = min x (34 - x) := hkx
        have h3 : min x (34 - x) = 17 := by omega
        by_cases hxle : x ≤ 34 - x
        · rw [min_eq_left hxle] at h3; omega
        · rw [min_eq_right (by omega)] at h3; omega
      have hy17 : y = 17 := by
        have h1 : (g y : ℤ) = 17 := by
          rw [← hkg]; exact_mod_cast hk17
        have h2 : (g y : ℤ) = min y (34 - y) := hky
        have h3 : min y (34 - y) = 17 := by omega
        by_cases hyle : y ≤ 34 - y
        · rw [min_eq_left hyle] at h3; omega
        · rw [min_eq_right (by omega)] at h3; omega
      rw [hx17, hy17]
    · have hk16 : g x ≤ 16 := by omega
      have hxor : x = (g x : ℤ) ∨ x = 34 - (g x : ℤ) := by
        have h1 : (g x : ℤ) = min x (34 - x) := hkx
        by_cases hxle : x ≤ 34 - x
        · rw [min_eq_left hxle] at h1; exact Or.inl h1.symm
        · rw [min_eq_right (by omega)] at h1; exact Or.inr (by omega)
      have hyor : y = (g y : ℤ) ∨ y = 34 - (g y : ℤ) := by
        have h1 : (g y : ℤ) = min y (34 - y) := hky
        by_cases hyle : y ≤ 34 - y
        · rw [min_eq_left hyle] at h1; exact Or.inl h1.symm
        · rw [min_eq_right (by omega)] at h1; exact Or.inr (by omega)
      have hne : (g x : ℤ) ≠ 34 - (g x : ℤ) := by
        intro hc; omega
      have hkx' : (g y : ℤ) = (g x : ℤ) := by
        rw [← hkg]
      rcases hxor with hxe | hxe
      · rcases hyor with hye | hye
        · rw [hxe, hye, hkg]
        · rw [hxe, hye, hkx']
          exfalso
          apply hne
          exact (hno x hx y hy (by omega) (by omega)).elim
      · rcases hyor with hye | hye
        · rw [hxe, hye, hkx']
          exfalso
          apply hne
          exact (hno x hx y hy (by omega) (by omega)).elim
        · rw [hxe, hye, hkg]
  have hsub : A.image g ⊆ Finset.range 18 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (hrange x hx)
  have heq : (A.image g).card = A.card :=
    Finset.card_image_of_injOn (by simpa using hI)
  have hbound : (A.image g).card ≤ 18 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hA_le : A.card ≤ 18 := by
    rw [← heq]; exact hbound
  omega

-- Cardinality transfer between T ⊆ S and its index set A.

/-
Informal proof sketch.

Write S = {3j + 1 | j ∈ ℤ, 0 ≤ j ≤ 33}.  Thus S has 34 elements indexed by
the integers 0,1,...,33.  Given T ⊆ S with |T| = 20, let A be the set of
indices j ∈ {0,...,33} such that 3j+1 ∈ T.  Then |A| = |T| = 20.

Two elements 3i+1 and 3j+1 of T sum to 104 iff 3(i+j)+2 = 104, i.e. iff
i+j = 34.  Partition {0,...,33} into the 17 pairs {0,34}, {1,33}, ...,
{16,18}, together with the singleton {17}; equivalently, there are 18
"blocks" such that two distinct indices in the same block sum to 34.
If A contained no two distinct indices summing to 34, then A would contain
at most one index from each of these 18 blocks, so |A| ≤ 18.  But |A| = 20,
contradiction.  Hence there exist distinct i,j ∈ A with i+j = 34, and then
m = 3i+1 and n = 3j+1 are distinct elements of T with m+n = 104.
-/

-- Combinatorial core: a subset of {0,...,33} of size 20 contains two distinct

-- indices summing to 34.

-- Cardinality transfer between T ⊆ S and its index set A.

/-
Informal proof sketch.

Write S = {3j + 1 | j ∈ ℤ, 0 ≤ j ≤ 33}.  Thus S has 34 elements indexed by
the integers 0,1,...,33.  Given T ⊆ S with |T| = 20, let A be the set of
indices j ∈ {0,...,33} such that 3j+1 ∈ T.  Then |A| = |T| = 20.

Two elements 3i+1 and 3j+1 of T sum to 104 iff 3(i+j)+2 = 104, i.e. iff
i+j = 34.  Partition {0,...,33} into the 17 pairs {0,34}, {1,33}, ...,
{16,18}, together with the singleton {17}; equivalently, there are 18
"blocks" such that two distinct indices in the same block sum to 34.
If A contained no two distinct indices summing to 34, then A would contain
at most one index from each of these 18 blocks, so |A| ≤ 18.  But |A| = 20,
contradiction.  Hence there exist distinct i,j ∈ A with i+j = 34, and then
m = 3i+1 and n = 3j+1 are distinct elements of T with m+n = 104.
-/

-- Combinatorial core: a subset of {0,...,33} of size 20 contains two distinct

-- indices summing to 34.

-- Cardinality transfer between T ⊆ S and its index set A.

theorem A_card (S T : Set ℤ) (A : Finset ℤ)
    (hS : S = {k | ∃ j : ℤ, 0 ≤ j ∧ j ≤ 33 ∧ k = 3 * j + 1})
    (hTsub : T ⊆ S)
    (hA : ∀ j : ℤ, j ∈ A ↔ (0 ≤ j ∧ j ≤ 33 ∧ (3 * j + 1) ∈ T)) :
    A.card = T.ncard := by
  have hT_eq : T = (Finset.image (fun j : ℤ => 3 * j + 1) A : Set ℤ) := by
    first | (omega; done) | (linarith; done) | (positivity; done) | (norm_num; done) | (simp_all; done) | (ring; done) | ((field_simp; ring); done) | (nlinarith [sq_nonneg (0:ℤ)]; done) | (grind; done) | (aesop; done)
  have hcard : (Finset.image (fun j : ℤ => 3 * j + 1) A).card = A.card := by
    apply Finset.card_image_of_injOn
    intro x _ y _ h
    linarith
  rw [hT_eq]
  rw [Set.ncard_coe_finset]
  exact hcard.symm

/--
Let $S = \{1, 4, 7, 10, 13, 16, \dots , 100\}$. Let $T$ be a subset of $20$ elements of $S$. Show that we can find two distinct elements of $T$ with sum $104$.
-/
theorem putnam_1978_a1
(S T : Set ℤ)
(hS : S = {k | ∃ j : ℤ, 0 ≤ j ∧ j ≤ 33 ∧ k = 3 * j + 1})
(hT : T ⊆ S ∧ T.ncard = 20)
: (∃ m ∈ T, ∃ n ∈ T, m ≠ n ∧ m + n = 104) := by
  classical
  rcases hT with ⟨hTsub, hTcard⟩
  let A := (Finset.Icc (0 : ℤ) 33).filter (fun j => (3 * j + 1) ∈ T)
  have hAx : ∀ j : ℤ, j ∈ A ↔ (0 ≤ j ∧ j ≤ 33 ∧ (3 * j + 1) ∈ T) := by
    intro j
    simp only [A, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hAsub : A ⊆ Finset.Icc (0 : ℤ) 33 := by
    intro j hj
    have h := (hAx j).mp hj
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  have hcard : A.card = 20 :=
    ((A_card S T A hS hTsub hAx).trans hTcard)
  obtain ⟨i, hi, j, hj, hij, hsum⟩ := index_pair_lemma A hAsub hcard
  refine ⟨3 * i + 1, ?_, 3 * j + 1, ?_, ?_, ?_⟩
  · exact ((hAx i).mp hi).2.2
  · exact ((hAx j).mp hj).2.2
  · intro h
    apply hij
    linarith
  · have h1 : (3 * i + 1) + (3 * j + 1) = 3 * (i + j) + 2 := by ring
    rw [h1, hsum]
    norm_num

#print axioms putnam_1978_a1
