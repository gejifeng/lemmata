import Mathlib
open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk


open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

theorem putnam1965b5_nat_bound (V E : ℕ) (hE : 4 * E ≤ V ^ 2) :
    E ≤ (V / 2) * (V - V / 2) := by
  let q := V / 2
  let r := V % 2
  have hq : V / 2 = q := rfl
  have hmod : V % 2 = r := rfl
  have hV : V = 2 * q + r := by
    have h := Nat.div_add_mod V 2
    rw [hq, hmod] at h
    omega
  have hr : r < 2 := Nat.mod_lt V (by norm_num)
  have hr2 : r * r < 4 := by
    have hle : r ≤ 1 := by omega
    have : r * r ≤ 1 := by
      calc r * r ≤ 1 * 1 := Nat.mul_le_mul hle hle
         _ = 1 := by norm_num
    exact Nat.lt_of_le_of_lt this (by norm_num)
  have hsq : V ^ 2 = 4 * (q * (q + r)) + r * r := by
    rw [hV]
    ring
  rw [hsq] at hE
  have h_main : E ≤ q * (q + r) := by
    by_contra h
    have hlt : q * (q + r) < E := Nat.lt_of_not_le h
    have hA : q * (q + r) + 1 ≤ E := by omega
    have h1 : 4 * (q * (q + r) + 1) ≤ 4 * E :=
      Nat.mul_le_mul (Nat.le_refl 4) hA
    have h3 : 4 * (q * (q + r)) + r * r < 4 * (q * (q + r) + 1) := by
      have : 4 * (q * (q + r) + 1) = 4 * (q * (q + r)) + 4 := by ring
      rw [this]
      exact Nat.add_lt_add_left hr2 _
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h1 hE) h3)
  have hRHS : (V / 2) * (V - V / 2) = q * (q + r) := by
    rw [hq]
    have : V - q = q + r := by
      rw [hV]
      omega
    rw [this]
  rwa [hRHS]

theorem putnam1965b5_finset_exists_subset_card {α : Type*} [DecidableEq α] (S : Finset α) (n : ℕ)
    (hn : n ≤ S.card) : ∃ T : Finset α, T ⊆ S ∧ T.card = n := by
  exact Finset.exists_subset_card_eq hn

theorem putnam1965b5_nat_card_eq_fintype_card {K : Type*} [Fintype K] :
    Nat.card K = Fintype.card K := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open Finset Sym2

theorem putnam1965b5_exists_bipartite_edge_set {K : Type*} [Fintype K] [DecidableEq K] (V : ℕ)
    (hcard : Fintype.card K = V) :
    ∃ (A B : Finset K) (S : Finset (Sym2 K)),
      A ∪ B = Finset.univ ∧
      Disjoint A B ∧
      S = (Finset.product A B).image (fun p => Sym2.mk (p.1, p.2)) ∧
      A.card = V / 2 ∧
      B.card = V - V / 2 ∧
      S.card = (V / 2) * (V - V / 2) := by
  have hV : (Finset.univ : Finset K).card = V := by
    simp [hcard]
  obtain ⟨A, hA_sub, hA_card⟩ :=
    putnam1965b5_finset_exists_subset_card (Finset.univ : Finset K) (V / 2) (by
      rw [hV]
      exact Nat.div_le_self V 2)
  let B : Finset K := Finset.univ \ A
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    simp only [B, Finset.mem_sdiff] at hxB
    exact hxB.2 hx
  have hunion : A ∪ B = Finset.univ := by
    ext x
    by_cases hx : x ∈ A
    · simp [B, hx]
    · simp [B, hx]
  have hBcard : B.card = V - V / 2 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, hV, hA_card] at h
    omega
  let S : Finset (Sym2 K) := (Finset.product A B).image (fun p => Sym2.mk (p.1, p.2))
  have hcardS : S.card = (A ×ˢ B).card := by
    have hS : S = (A ×ˢ B).image (fun p => Sym2.mk (p.1, p.2)) := rfl
    rw [hS]
    refine Finset.card_image_of_injOn ?_
    intro p hp q hq h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    obtain ⟨ha, hb⟩ := (Finset.mem_product.mp hp)
    obtain ⟨hc, hd⟩ := (Finset.mem_product.mp hq)
    rw [Sym2.mk_eq_mk_iff] at h
    cases h with
    | inl h =>
        have h1 : a = c := (Prod.mk.inj h).1
        have h2 : b = d := (Prod.mk.inj h).2
        subst h1; subst h2; rfl
    | inr h =>
        have h1 : a = d := (Prod.mk.inj h).1
        have h2 : b = c := (Prod.mk.inj h).2
        have hdA : d ∈ A := by
          rwa [← h1]
        exact absurd hd (Finset.disjoint_left.mp hdisj hdA)
  have hProd : (A ×ˢ B).card = A.card * B.card := by
    rw [Finset.card_product]
  have hScard : S.card = (V / 2) * (V - V / 2) := by
    rw [hcardS, hProd, hA_card, hBcard]
  exact ⟨A, B, S, hunion, hdisj, rfl, hA_card, hBcard, hScard⟩

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

theorem putnam1965b5_exists_bipartite_graph {K : Type*} [Fintype K] [DecidableEq K]
    {A B : Finset K} {T : Finset (Sym2 K)}
    (hdisj : Disjoint A B)
    (hT : T ⊆ (Finset.product A B).image (fun p => Sym2.mk (p.1, p.2))) :
    ∃ G : SimpleGraph K,
      G.edgeSet = (T : Set (Sym2 K)) ∧
      ∀ x y : K, G.Adj x y → (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A) := by
  let G : SimpleGraph K :=
    { Adj := fun x y => (Sym2.mk (x, y) : Sym2 K) ∈ (T : Set (Sym2 K))
      symm := by
        intro x y h
        have hsym : Sym2.mk (y, x) = Sym2.mk (x, y) := by
          rw [Sym2.mk_eq_mk_iff]
          exact Or.inr rfl
        rw [hsym]
        exact h
      loopless := by
        constructor
        intro x hx
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp (hT hx)
        obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
        rw [Sym2.mk_eq_mk_iff] at he
        cases he with
        | inl hpe =>
            obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
            subst h1
            rw [← h2] at hpA
            exact hdisj.notMem_of_mem_right_finset hpB hpA
        | inr hpe =>
            simp at hpe
            obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
            subst h1
            rw [← h2] at hpA
            exact hdisj.notMem_of_mem_right_finset hpB hpA }
  refine ⟨G, ?_, ?_⟩
  · ext e
    refine Sym2.inductionOn e ?_
    intro x y
    rw [SimpleGraph.mem_edgeSet]
  · intro x y h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp (hT h)
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
    rw [Sym2.mk_eq_mk_iff] at he
    cases he with
    | inl hpe =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
        subst h1
        subst h2
        exact Or.inl ⟨hpA, hpB⟩
    | inr hpe =>
        simp at hpe
        obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
        subst h1
        subst h2
        exact Or.inr ⟨hpB, hpA⟩

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

open EuclideanGeometry Topology Filter Complex SimpleGraph.Walk

theorem putnam1965b5_bipartite_no_walk3 {K : Type*} [Fintype K] [DecidableEq K] (G : SimpleGraph K)
    (A B : Finset K)
    (hunion : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ x y : K, G.Adj x y → (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) :
    ∀ a : K, ∀ w : G.Walk a a, w.length ≠ 3 := by
  intro a w hlen
  have hmem : ∀ x : K, x ∈ A ∨ x ∈ B := by
    intro x
    have hx : x ∈ A ∪ B := by
      rw [hunion]
      exact Finset.mem_univ x
    exact Finset.mem_union.mp hx
  have hdisj' : ∀ x : K, x ∈ A → x ∉ B := by
    intro x hx hxb
    have h := Finset.mem_inter.mpr ⟨hx, hxb⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at h
    exact absurd h (by simp)
  have hdisj'' : ∀ x : K, x ∈ B → x ∉ A := by
    intro x hx hxa
    have h := Finset.mem_inter.mpr ⟨hxa, hx⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at h
    exact absurd h (by simp)
  have edgeAB : ∀ x y : K, G.Adj x y → x ∈ A → y ∈ B := by
    intro x y h hxA
    rcases hcross x y h with ⟨_, hyB⟩ | ⟨hxB, _⟩
    · exact hyB
    · exact absurd hxB (hdisj' x hxA)
  have edgeBA : ∀ x y : K, G.Adj x y → x ∈ B → y ∈ A := by
    intro x y h hxB
    rcases hcross x y h with ⟨hxA, _⟩ | ⟨_, hyA⟩
    · exact absurd hxA (hdisj'' x hxB)
    · exact hyA
  cases w with
  | nil =>
      simp at hlen
  | cons h1 w1 =>
      simp only [SimpleGraph.Walk.length_cons] at hlen
      have h1len : w1.length = 2 := by omega
      cases w1 with
      | nil =>
          simp at h1len
      | cons h2 w2 =>
          simp only [SimpleGraph.Walk.length_cons] at h1len
          have h2len : w2.length = 1 := by omega
          cases w2 with
          | nil =>
              simp at h2len
          | cons h3 w3 =>
              simp only [SimpleGraph.Walk.length_cons] at h2len
              have h3len : w3.length = 0 := by omega
              cases w3 with
              | nil =>
                  rcases hmem a with haA | haB
                  · have hbB := edgeAB _ _ h1 haA
                    have hcA := edgeBA _ _ h2 hbB
                    have haB := edgeAB _ _ h3 hcA
                    exact absurd haB (hdisj' a haA)
                  · have hbA := edgeBA _ _ h1 haB
                    have hcB := edgeAB _ _ h2 hbA
                    have haA := edgeBA _ _ h3 hcB
                    exact absurd haA (hdisj'' a haB)
              | cons h4 w4 =>
                  simp only [SimpleGraph.Walk.length_cons] at h3len
                  omega

theorem putnam1965b5_set_ncard_eq_finset_card {α : Type*} (s : Finset α) :
    (s : Set α).ncard = s.card := by
  intros
  first
  | (omega; done)
  | (linarith; done)
  | (positivity; done)
  | (norm_num; done)
  | (simp_all; done)
  | (ring; done)
  | (decide; done)

/--
Prove that, if $4E \le V^2$, there exists a graph with $E$ edges and $V$ vertices with no triangles (cycles of length $3$).
-/
theorem putnam_1965_b5
{K : Type*}
[Fintype K]
(V E : ℕ)
(hV : V = Nat.card K)
(hE: 4*E ≤ V^2)
: ∃ G : SimpleGraph K, G.edgeSet.ncard = E ∧ ∀ a : K, ∀ w : G.Walk a a, w.length ≠ 3 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hcard : Fintype.card K = V := by
    rw [← putnam1965b5_nat_card_eq_fintype_card, hV]
  obtain ⟨A, B, S, hunion, hdisj, hSdef, hAcard, hBcard, hScard⟩ :=
    putnam1965b5_exists_bipartite_edge_set V hcard
  have hEBound : E ≤ S.card := by
    rw [hScard]
    exact putnam1965b5_nat_bound V E hE
  obtain ⟨T, hTsub, hTcard⟩ :=
    putnam1965b5_finset_exists_subset_card S E hEBound
  have hTsubImg : T ⊆ (Finset.product A B).image (fun p => Sym2.mk (p.1, p.2)) := by
    rw [← hSdef]
    exact hTsub
  obtain ⟨G, hGedge, hGcross⟩ :=
    putnam1965b5_exists_bipartite_graph hdisj hTsubImg
  use G
  refine ⟨?_, ?_⟩
  · rw [hGedge, putnam1965b5_set_ncard_eq_finset_card (α := Sym2 K) T, hTcard]
  · exact putnam1965b5_bipartite_no_walk3 G A B hunion hdisj hGcross

#print axioms putnam_1965_b5
