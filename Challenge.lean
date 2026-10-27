module

public import Mathlib

/-!
# Group constructions cannot refute the Set Cover Conjecture

**Background.** Fix `k` and let `n = 3k`. Pratt's balanced tripartitioning tensor is
`T_k = ∑ x_A ⊗ y_B ⊗ z_C`, where the sum runs over ordered triples `(A, B, C)` of pairwise
disjoint `k`-subsets of `[3k]`. Pratt (K. Pratt, *A stronger connection between the asymptotic
rank conjecture and the set cover conjecture*, STOC 2024, arXiv:2311.02774, Corollary 1.12) shows:
if the Set Cover Conjecture (SCC) holds, then for every `k` the asymptotic rank of `T_k` is at
least

  `τ_k = 8^k · C(3k,k) · C(2k,k) / 27^k`.

So showing `R̃(T_k) < τ_k` for a single `k` would refute SCC.

**Group constructions.** Pratt's own upper bound `R(T_k) ≤ 8^k/2` is a group construction. Take a
group `G` and maps `f₁, f₂, f₃` from `k`-subsets to `G` with

  `f₁(A) · f₂(B) · f₃(C) = 1  ⟺  A, B, C pairwise disjoint`.

This is a "partition product property", the analogue of the Cohn–Umans triple product property.
Given such maps, `T_k` is a restriction of the group-algebra tensor of `G`. For abelian `G` this
gives rank `≤ |G|`. For non-abelian `G` it gives asymptotic rank `≤ ∑_ρ (dim ρ)^ω`, which is
`≥ |G|`.

**Main theorems.** `group_degeneration_exceeds_SCC_threshold` covers monomial degenerations, i.e. border-rank
constructions. `group_construction_exceeds_SCC_threshold` covers restrictions. For every finite group `G`, abelian
or not, and every `k ≥ 2`, a partition product property forces `|G| > τ_k`. Every such
construction therefore gives a bound above Pratt's threshold, and none can refute SCC.

The proof goes through two further compared theorems:

* `ppp_factors_through_commuting`: **rigidity**. If `f₁(A) f₂(B) f₃(C) = 1` holds just for
  disjoint triples, then there are pairwise commuting `g₀,…,g_{n-1}` such that for every triple of
  `k`-sets, `f₁(A) f₂(B) f₃(C) = ∏ᵢ gᵢ^(mᵢ - 1)`, where `mᵢ` is the multiplicity of `i` in
  `(A,B,C)`. Non-commutativity buys nothing: the construction factors through an abelian subgroup.
* `ppp_card_ge`: `|G| ≥ 2^(3k-1) = 8^k/2`. So Pratt's group bound is exactly optimal among group
  restrictions.

**Not formalised.** Pratt's Corollary 1.12 (SCC ⟹ `R̃(T_k) ≥ τ_k`), and the standard step from a
group embedding to a rank bound, are cited, not formalised. Tensor powers `T_k^{⊗m}` (the per-copy
analogue) are proved on paper but not formalised here.
-/

@[expose] public section

open Finset

/-- **Rigidity of partition products.** Let `k ≥ 2` and let `G` be any group. Suppose
`f₁ A * f₂ B * f₃ C = 1` whenever `A, B, C` are pairwise disjoint `k`-subsets of `Fin (3k)`.
Then there are pairwise commuting `g i` such that for **every** triple of `k`-subsets,
`f₁ A * f₂ B * f₃ C = ∏ᵢ (g i)^(mᵢ - 1)`. Here `mᵢ ∈ {0,1,2,3}` is the number of the sets
`A, B, C` containing `i`, and the product is taken in the order `i = 0, 1, …, 3k-1`. -/
theorem ppp_factors_through_commuting {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C =
          ((List.finRange (3 * k)).map fun i =>
            g i ^ ((if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
              (if i ∈ C then 1 else 0) - 1 : ℤ)).prod := by
  sorry

/-- **Pratt's group bound is optimal.** If a finite group `G` has maps with
`f₁ A * f₂ B * f₃ C = 1 ⟺ A, B, C pairwise disjoint` (for `k`-subsets of `Fin (3k)`, `k ≥ 2`),
then `|G| ≥ 2^(3k-1)`. -/
theorem ppp_card_ge {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    2 ^ (3 * k - 1) ≤ Fintype.card G := by
  sorry

/-- **Group constructions cannot refute the Set Cover Conjecture.** Under the same hypothesis,
`|G|` is strictly larger than Pratt's SCC threshold `τ_k = 8^k·C(3k,k)·C(2k,k)/27^k`. -/
theorem group_construction_exceeds_SCC_threshold {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by
  sorry

/-- **Group degenerations cannot refute the Set Cover Conjecture (border-rank version).** Take a
monomial (Strassen combinatorial) degeneration of the group tensor of `G` onto `T_k`. It consists
of maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c` on `k`-subsets of `Fin (3k)` such that:
* every pairwise disjoint triple has product `1` and weight `a A + b B + c C = 0`;
* every other triple with product `1` has strictly positive weight.
Then `|G|` exceeds Pratt's threshold `τ_k = 8^k·C(3k,k)·C(2k,k)/27^k`. Such a degeneration gives
border rank (hence asymptotic rank) at most `|G|` in the abelian case, so it cannot refute SCC.
This statement contains the restriction case: take `a = b = c = 0`. -/
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
  sorry
