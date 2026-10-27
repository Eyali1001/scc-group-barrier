module

public import Mathlib
public import SCCThm8.Rigidity
public import SCCThm8.Counting
public import SCCThm8.Numeric
public import SCCThm8.Degeneration

/-!
# Solution

These are the `Challenge` declarations, proved from `SCCThm8.Rigidity` (non-abelian rigidity),
`SCCThm8.Counting` (realisability and the lift lemma) and `SCCThm8.Numeric` (Pratt's threshold).
-/

@[expose] public section

open Finset

/-- Three pairwise disjoint `k`-subsets of `Fin (3k)` cover every point exactly once. -/
theorem mult_eq_one_of_disjoint (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    SCCThm8.mult A B C i = 1 := by
  have hU : A ∪ B ∪ C = univ := by
    apply Finset.eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hAC, hBC⟩),
      card_union_of_disjoint hAB, hA, hB, hC, Fintype.card_fin]
    ring
  have hi : i ∈ A ∪ B ∪ C := hU ▸ mem_univ i
  simp only [mem_union] at hi
  unfold SCCThm8.mult
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;>
    simp_all [Finset.disjoint_left]

theorem ppp_factors_through_commuting {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C =
          ((List.finRange (3 * k)).map fun i =>
            g i ^ ((if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
              (if i ∈ C then 1 else 0) - 1 : ℤ)).prod :=
  SCCThm8.rigidity k hk f₁ f₂ f₃ hP

theorem ppp_card_ge {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    2 ^ (3 * k - 1) ≤ Fintype.card G := by
  obtain ⟨g, hc, hprod⟩ := SCCThm8.rigidity k hk f₁ f₂ f₃
    (fun A B C hA hB hC h1 h2 h3 => (hPPP A B C hA hB hC).mpr ⟨h1, h2, h3⟩)
  refine SCCThm8.card_bound (by omega) g hc ?_
  intro e hr hs hne h1
  obtain ⟨A, B, C, hA, hB, hC, hm⟩ := SCCThm8.realizable k (fun i => e i + 1)
    (fun i => by have := hr i; constructor <;> omega)
    (by rw [Finset.sum_add_distrib, hs]; simp)
  have hone : f₁ A * f₂ B * f₃ C = 1 := by
    rw [hprod A B C hA hB hC]
    have : (fun i => SCCThm8.mult A B C i - 1) = e := by
      funext i; rw [hm i]; ring
    rw [this]; exact h1
  obtain ⟨h1', h2', h3'⟩ := (hPPP A B C hA hB hC).mp hone
  apply hne
  funext i
  have := mult_eq_one_of_disjoint k A B C hA hB hC h1' h2' h3' i
  rw [hm i] at this
  simp only [Pi.zero_apply]
  omega

theorem group_construction_exceeds_SCC_threshold {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by
  have h1 := SCCThm8.tau_lt_two_pow k hk
  have h2 := ppp_card_ge k hk f₁ f₂ f₃ hPPP
  have h2' : ((2 ^ (3 * k - 1) : ℕ) : ℚ) ≤ (Fintype.card G : ℚ) := by exact_mod_cast h2
  unfold SCCThm8.tau at h1
  push_cast at h2'
  linarith

theorem group_degeneration_exceeds_SCC_threshold {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G) (a b c : Finset (Fin (3 * k)) → ℤ)
    (hpart : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      ¬ (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by
  have h1 := SCCThm8.tau_lt_central k (by omega)
  have h2 := SCCThm8.deg_card_ge k hk f₁ f₂ f₃ a b c hpart hnon
  have h2' : ((Nat.choose (3 * k) (3 * k / 2) : ℕ) : ℚ) ≤ (Fintype.card G : ℚ) := by
    exact_mod_cast h2
  unfold SCCThm8.tau at h1
  linarith
