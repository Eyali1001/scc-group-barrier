# Single-copy group constructions cannot refute the Set Cover Conjecture (Lean)

## Headline

**`group_degeneration_exceeds_SCC_threshold`** (border-rank version). Let `G` be any finite group,
abelian or not, and let `k ≥ 2`. Take a Strassen combinatorial degeneration of the group tensor of
`G` onto Pratt's tensor `T_k`. That is:
* maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c` on `k`-subsets;
* every disjoint triple has product `1` and weight `0`;
* every other triple with product `1` has positive weight.

Then `|G| > τ_k = 8^k·C(3k,k)·C(2k,k)/27^k`. The proof goes through `|G| ≥ C(3k,⌊3k/2⌋)`.

**`group_construction_exceeds_SCC_threshold`** (restriction version). Let `G` be any finite group, abelian or not, and let `k ≥ 2`.
Suppose maps `f₁, f₂, f₃` from the `k`-subsets of `{0, …, 3k−1}` to `G` satisfy

    f₁(A) · f₂(B) · f₃(C) = 1   ⟺   A, B, C are pairwise disjoint.

Then `|G| > τ_k = 8^k·C(3k,k)·C(2k,k)/27^k`.

### Why this is the Set Cover Conjecture (SCC) threshold

Pratt (STOC 2024, arXiv:2311.02774, Cor. 1.12) shows that SCC implies `R̃(T_k) ≥ τ_k` for every `k`.
Here `T_k` is the balanced tripartitioning tensor. A refutation of SCC through `T_k` therefore needs
`R̃(T_k) < τ_k` for some `k`.

A group construction like the one above realises `T_k` inside the group tensor of `G`. That gives
`R̃(T_k) ≤ |G|` for abelian `G`, and `≤ ∑_ρ dim(ρ)^ω`, which is at least `|G|`, for non-abelian `G`.
By the theorem, every such bound exceeds `τ_k`. Pratt's group method uses `G = ℤ₂^(3k−1)`.

## Supporting theorems (also compared)

* **`ppp_factors_through_commuting`** (rigidity). Assume only that disjoint triples have product `1`.
  * Then there are pairwise commuting `gᵢ` with `f₁(A)f₂(B)f₃(C) = ∏ᵢ gᵢ^(mᵢ−1)` for every triple of
    `k`-sets, where `m` is the multiplicity vector.
  * So the construction lives in an abelian subgroup, and non-commutativity gives no advantage. This
    contrasts with the Cohn–Umans approach to matrix multiplication.
  * Key steps: the swap derivative `f₁(A−i+j)f₁(A)⁻¹` is independent of `A`, by Kneser-type
    connectivity. Then a two-swap identity forces the swap derivatives to commute.
* **`ppp_card_ge`** (`|G| ≥ 2^(3k−1)`, via a lift lemma on even subsets). Pratt's `8^k/2` is exactly
  optimal among group restrictions.

## Scope

* **Not formalised:**
  * Pratt's Corollary 1.12.
  * The standard step from a group embedding to a rank bound.
* **What is bounded.** The theorems bound the *size of the group* a construction needs. They also bound the
  rank bounds such constructions inherit from their ambient group tensors. They are **not** lower bounds on the
  rank or border rank of `T_k` itself. Arbitrary linear maps and other non-group constructions are untouched.
* **Single copy only.** Only constructions for one copy of `T_k` are covered.
  * A refutation of SCC needs an *asymptotic*-rank bound, so it could also come from a joint group
    construction for `T_k^{⊗m}` that beats `|G|^{1/m}`.
  * Closing that case needs a tensor-power version of these theorems: block-wise rigidity, with per-copy
    bound `C(3k,⌊3k/2⌋)`.
  * We have a proof sketch of that version, but it is **not** written up or formalised here.
  * The headline is therefore "no single-copy group construction can refute SCC".
* **What the theorem does not say.** It does **not** say SCC is true.
* **Novelty:**
  * A literature search found the `ℤ₂`-only special case of the counting bound in a public dataset.
  * We found no statement of the rigidity theorem for general groups. The search was not exhaustive.

## Files

| File | Contents |
|---|---|
| `Challenge.lean` | The statements, depending on Mathlib only. |
| `Solution.lean` | The proofs, which use `SCCThm8/{Rigidity,Counting,Degeneration,Numeric}.lean`. |

* **Axioms:** `propext`, `Classical.choice`, `Quot.sound`.
* **Toolchain:** Lean `v4.35.0`, Mathlib `v4.35.0`.

## Production and review

The statements, informal proofs and Lean proofs were produced by AI coding agents (Anthropic Claude),
directed by the human author(s) listed in `formalization.yaml`.

No independent human mathematical review has been performed. The informal proofs were cross-checked by
independent agent runs and by exhaustive computation (SAT over all groups of order ≤ 31 for `k = 2`).

## Licence

Apache-2.0.
