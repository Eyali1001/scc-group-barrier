module

public import SCCThm8.PowerRigidity
public import SCCThm8.Counting
public import SCCThm8.Degeneration

@[expose] public section

namespace SCCThm8

open Finset

/-- An element commuting with every `g i` commutes with `psi g e`. -/
theorem commute_psi {G : Type*} [Group G] {n : ℕ} {x : G} (g : Fin n → G)
    (h : ∀ i, Commute x (g i)) (e : Fin n → ℤ) : Commute x (psi g e) :=
  Commute.list_prod_right _ _ (fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (h i).zpow_right _)

/-- For a commuting family, `psiP g` is additive. -/
theorem psiP_add {G : Type*} [Group G] {m n : ℕ} (g : Fin m → Fin n → G)
    (hc : ∀ j i j' i', Commute (g j i) (g j' i')) (e e' : Fin m → Fin n → ℤ) :
    psiP g (e + e') = psiP g e * psiP g e' := by
  unfold psiP
  have h : ∀ j, psi (g j) ((e + e') j) = psi (g j) (e j) * psi (g j) (e' j) := fun j =>
    psi_add (g j) (fun i i' => hc j i j i') (e j) (e' j)
  simp only [h]
  exact list_prod_map_mul_of_commute _ (fun j => psi (g j) (e j)) (fun j => psi (g j) (e' j))
    (fun j j' => commute_psi (g j') (fun i' => (commute_psi (g j) (fun i => hc j' i' j i)
      (e j)).symm) (e' j'))

/-- In `Multiplicative ℤ`, `psiP` is a linear form in the exponents. -/
theorem toAdd_psiP {m n : ℕ} (u : Fin m → Fin n → Multiplicative ℤ) (e : Fin m → Fin n → ℤ) :
    Multiplicative.toAdd (psiP u e) = ∑ j, ∑ i, e j i * Multiplicative.toAdd (u j i) := by
  have : Multiplicative.toAdd (psiP u e) = ∑ j, Multiplicative.toAdd (psi (u j) (e j)) := by
    unfold psiP
    rw [Fin.sum_univ_def]
    generalize List.finRange m = l
    induction l with
    | nil => rfl
    | cons x l ih => simp [List.map_cons, List.prod_cons, toAdd_mul, ih]
  rw [this]
  exact sum_congr rfl fun j _ => toAdd_psi (u j) (e j)

/-- **Degeneration bound for `T_k^{⊗m}`.** Take a monomial degeneration of the group tensor of `G`
onto `T_k^{⊗m}`. It consists of maps `f₁, f₂, f₃` into `G` and integer weights `a, b, c` on
`m`-tuples of `k`-subsets of `Fin (3k)` such that:
* blockwise-disjoint triples have product `1` and weight `0`;
* every other triple with product `1` has positive weight.
Then `|G| ≥ C(3k, ⌊3k/2⌋)^m`. -/
theorem power_deg_card_ge {G : Type*} [Group G] [Fintype G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) (a b c : (Fin m → Finset (Fin (3 * k))) → ℤ)
    (hpart : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    Nat.choose (3 * k) (3 * k / 2) ^ m ≤ Fintype.card G := by
  -- Step 1: rigidity in `G`.
  obtain ⟨g, hc, hprod⟩ := power_rigidity k m hk f₁ f₂ f₃ (fun A B C hA hB hC hd =>
    (hpart A B C hA hB hC hd).1)
  -- Step 2: rigidity in `Multiplicative ℤ` for the weights.
  obtain ⟨u, -, hw⟩ := power_rigidity (G := Multiplicative ℤ) k m hk
    (fun A => Multiplicative.ofAdd (a A)) (fun B => Multiplicative.ofAdd (b B))
    (fun C => Multiplicative.ofAdd (c C)) (fun A B C hA hB hC hd => by
      have := (hpart A B C hA hB hC hd).2
      rw [← ofAdd_add, ← ofAdd_add, this, ofAdd_zero])
  set W : (Fin m → Fin (3 * k) → ℤ) → ℤ :=
    fun e => ∑ j, ∑ i, e j i * Multiplicative.toAdd (u j i) with hW
  have hweight : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      a A + b B + c C = W (fun j i => multP A B C j i - 1) := by
    intro A B C hA hB hC
    have := congrArg Multiplicative.toAdd (hw A B C hA hB hC)
    rw [toAdd_psiP] at this
    simpa [toAdd_mul] using this
  -- Step 3: a nonzero blockwise-balanced `{-1,0,1}` array killed by `psiP g` has positive weight.
  have key : ∀ d : Fin m → Fin (3 * k) → ℤ, (∀ j i, -1 ≤ d j i ∧ d j i ≤ 1) →
      (∀ j, ∑ i, d j i = 0) → d ≠ 0 → psiP g d = 1 → 0 < W d := by
    intro d hd hs hne h1
    have hr : ∀ j, ∃ A B C : Finset (Fin (3 * k)), A.card = k ∧ B.card = k ∧ C.card = k ∧
        ∀ i, mult A B C i = d j i + 1 := fun j =>
      realizable k (fun i => d j i + 1)
        (fun i => by have := hd j i; constructor <;> omega)
        (by rw [sum_add_distrib, hs j]; simp)
    choose A B C hA hB hC hm using hr
    have hmd : (fun j i => multP A B C j i - 1) = d := by
      funext j i; simp only [multP]; rw [hm j i]; ring
    have hone : f₁ A * f₂ B * f₃ C = 1 := by
      rw [hprod A B C hA hB hC, hmd]; exact h1
    have hnp : ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) := by
      intro hdisj
      apply hne
      funext j i
      have := mult_eq_one_of_disj k (A j) (B j) (C j) (hA j) (hB j) (hC j)
        (hdisj j).1 (hdisj j).2.1 (hdisj j).2.2 i
      rw [hm j i] at this
      simp only [Pi.zero_apply]
      omega
    have := hnon A B C hA hB hC hnp hone
    rwa [hweight A B C hA hB hC, hmd] at this
  -- Step 4: injectivity on `m`-tuples of `(3k/2)`-subsets.
  have hinj : Set.InjOn (fun X : Fin m → Finset (Fin (3 * k)) => psiP g (fun j => ind (X j)))
      ↑(Fintype.piFinset fun _ : Fin m =>
        powersetCard (3 * k / 2) (univ : Finset (Fin (3 * k)))) := by
    intro X hX X' hX' heq
    rw [mem_coe, Fintype.mem_piFinset] at hX hX'
    simp only at heq
    by_contra hne
    set d : Fin m → Fin (3 * k) → ℤ := fun j i => ind (X j) i - ind (X' j) i with hd
    have e1 : psiP g (fun j => ind (X j)) = psiP g d * psiP g (fun j => ind (X' j)) := by
      rw [← psiP_add g hc]; congr 1; funext j i; simp [hd]
    have e2 : psiP g (fun j => ind (X' j)) = psiP g (-d) * psiP g (fun j => ind (X j)) := by
      rw [← psiP_add g hc]; congr 1; funext j i; simp [hd]
    have hd1 : psiP g d = 1 := mul_eq_right.mp (e1.symm.trans heq)
    have hd2 : psiP g (-d) = 1 := mul_eq_right.mp (e2.symm.trans heq.symm)
    have hb : ∀ j i, -1 ≤ d j i ∧ d j i ≤ 1 := by
      intro j i; simp only [hd, ind]; split_ifs <;> norm_num
    have hs : ∀ j, ∑ i, d j i = 0 := by
      intro j
      have h1 := (mem_powersetCard.mp (hX j)).2
      have h2 := (mem_powersetCard.mp (hX' j)).2
      simp only [hd]; rw [sum_sub_distrib, sum_ind, sum_ind, h1, h2, sub_self]
    have hne0 : d ≠ 0 := by
      intro h0
      apply hne
      funext j
      ext i
      have := congrFun (congrFun h0 j) i
      simp only [hd, ind, Pi.zero_apply] at this
      by_cases h1 : i ∈ X j <;> by_cases h2 : i ∈ X' j <;> simp [h1, h2] at this ⊢
    have p1 := key d hb hs hne0 hd1
    have p2 := key (-d)
      (fun j i => by have := hb j i; simp only [Pi.neg_apply]; constructor <;> omega)
      (fun j => by simp [sum_neg_distrib, hs j]) (neg_ne_zero.mpr hne0) hd2
    have : W (-d) = - W d := by simp [hW, sum_neg_distrib]
    omega
  have := card_le_card_of_injOn (t := (univ : Finset G)) _
    (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
  simpa [Fintype.card_piFinset, card_powersetCard] using this

end SCCThm8
