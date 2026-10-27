module

public import SCCThm8.Rigidity
public import SCCThm8.Counting

@[expose] public section

namespace SCCThm8

open Finset

/-- Three pairwise disjoint `k`-subsets of `Fin (3k)` cover every point exactly once. -/
theorem mult_eq_one_of_disj (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    mult A B C i = 1 := by
  have hU : A ∪ B ∪ C = univ := by
    apply Finset.eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hAC, hBC⟩),
      card_union_of_disjoint hAB, hA, hB, hC, Fintype.card_fin]
    ring
  have hi : i ∈ A ∪ B ∪ C := hU ▸ mem_univ i
  simp only [mem_union] at hi
  unfold mult
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;>
    simp_all [Finset.disjoint_left]

/-- In `Multiplicative ℤ`, `psi` is a linear form in the exponents. -/
theorem toAdd_psi {n : ℕ} (u : Fin n → Multiplicative ℤ) (e : Fin n → ℤ) :
    Multiplicative.toAdd (psi u e) = ∑ i, e i * Multiplicative.toAdd (u i) := by
  unfold psi
  rw [Fin.sum_univ_def]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.map_cons, List.prod_cons, toAdd_mul, ih, toAdd_zpow]

/-- The indicator vector of a finset, as integers. -/
def ind {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : ℤ := if i ∈ X then 1 else 0

theorem sum_ind {n : ℕ} (X : Finset (Fin n)) : ∑ i, ind X i = X.card := by
  unfold ind
  rw [sum_boole]
  simp

/-- **Degeneration bound.** Take a monomial (Strassen combinatorial) degeneration of the group
tensor of `G` onto `T_k`. It consists of maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c`
on `k`-subsets of `Fin (3k)` such that:
* partitions (pairwise disjoint triples) have product `1` and weight `0`;
* every other triple with product `1` has strictly positive weight.
Then `|G| ≥ C(3k, ⌊3k/2⌋)`. -/
theorem deg_card_ge {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G) (a b c : Finset (Fin (3 * k)) → ℤ)
    (hpart : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      ¬ (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    Nat.choose (3 * k) (3 * k / 2) ≤ Fintype.card G := by
  -- Step 1: rigidity in `G`.
  obtain ⟨g, hc, hprod⟩ := rigidity k hk f₁ f₂ f₃ (fun A B C hA hB hC h1 h2 h3 =>
    (hpart A B C hA hB hC h1 h2 h3).1)
  -- Step 2: rigidity in `Multiplicative ℤ` for the weights.
  obtain ⟨u, -, hw⟩ := rigidity (G := Multiplicative ℤ) k hk
    (fun A => Multiplicative.ofAdd (a A)) (fun B => Multiplicative.ofAdd (b B))
    (fun C => Multiplicative.ofAdd (c C)) (fun A B C hA hB hC h1 h2 h3 => by
      have := (hpart A B C hA hB hC h1 h2 h3).2
      rw [← ofAdd_add, ← ofAdd_add, this, ofAdd_zero])
  set W : (Fin (3 * k) → ℤ) → ℤ := fun e => ∑ i, e i * Multiplicative.toAdd (u i) with hW
  have hweight : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      a A + b B + c C = W (fun i => mult A B C i - 1) := by
    intro A B C hA hB hC
    have := congrArg Multiplicative.toAdd (hw A B C hA hB hC)
    rw [toAdd_psi] at this
    simpa [toAdd_mul] using this
  -- Step 3: a nonzero balanced `{-1,0,1}` vector killed by `psi g` has positive weight.
  have key : ∀ d : Fin (3 * k) → ℤ, (∀ i, -1 ≤ d i ∧ d i ≤ 1) → ∑ i, d i = 0 → d ≠ 0 →
      psi g d = 1 → 0 < W d := by
    intro d hd hs hne h1
    obtain ⟨A, B, C, hA, hB, hC, hm⟩ := realizable k (fun i => d i + 1)
      (fun i => by have := hd i; constructor <;> omega)
      (by rw [sum_add_distrib, hs]; simp)
    have hmd : (fun i => mult A B C i - 1) = d := by
      funext i; rw [hm i]; ring
    have hone : f₁ A * f₂ B * f₃ C = 1 := by
      rw [hprod A B C hA hB hC, hmd]; exact h1
    have hnp : ¬ (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) := by
      rintro ⟨h1', h2', h3'⟩
      apply hne
      funext i
      have := mult_eq_one_of_disj k A B C hA hB hC h1' h2' h3' i
      rw [hm i] at this
      simp only [Pi.zero_apply]
      omega
    have := hnon A B C hA hB hC hnp hone
    rwa [hweight A B C hA hB hC, hmd] at this
  -- Step 4: injectivity on the `(3k/2)`-subsets.
  have hinj : Set.InjOn (fun X : Finset (Fin (3 * k)) => psi g (ind X))
      ↑(powersetCard (3 * k / 2) (univ : Finset (Fin (3 * k)))) := by
    intro X hX X' hX' heq
    rw [mem_coe, mem_powersetCard] at hX hX'
    simp only at heq
    by_contra hne
    set d : Fin (3 * k) → ℤ := fun i => ind X i - ind X' i with hd
    have e1 : psi g (ind X) = psi g d * psi g (ind X') := by
      rw [← psi_add g hc]; congr 1; funext i; simp [hd]
    have e2 : psi g (ind X') = psi g (-d) * psi g (ind X) := by
      rw [← psi_add g hc]; congr 1; funext i; simp [hd]
    have hd1 : psi g d = 1 := by
      have := e1.symm.trans heq
      exact mul_eq_right.mp this
    have hd2 : psi g (-d) = 1 := by
      have := e2.symm.trans heq.symm
      exact mul_eq_right.mp this
    have hb : ∀ i, -1 ≤ d i ∧ d i ≤ 1 := by
      intro i; simp only [hd, ind]; split_ifs <;> norm_num
    have hs : ∑ i, d i = 0 := by
      simp only [hd]; rw [sum_sub_distrib, sum_ind, sum_ind, hX.2, hX'.2, sub_self]
    have hne0 : d ≠ 0 := by
      intro h0
      apply hne
      ext i
      have := congrFun h0 i
      simp only [hd, ind, Pi.zero_apply] at this
      by_cases h1 : i ∈ X <;> by_cases h2 : i ∈ X' <;> simp [h1, h2] at this ⊢
    have p1 := key d hb hs hne0 hd1
    have p2 := key (-d) (fun i => by have := hb i; simp only [Pi.neg_apply]; constructor <;> omega)
      (by simp [sum_neg_distrib, hs]) (neg_ne_zero.mpr hne0) hd2
    have : W (-d) = - W d := by simp [hW, sum_neg_distrib]
    omega
  have := card_le_card_of_injOn (t := (univ : Finset G)) _ (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
  simpa [card_powersetCard] using this

end SCCThm8
