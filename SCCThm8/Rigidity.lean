module

public import SCCThm8.Defs

@[expose] public section

namespace SCCThm8

open Finset

namespace Rig

variable {n : ℕ}

/-- The swap `A − i + j`. -/
def sw (A : Finset (Fin n)) (i j : Fin n) : Finset (Fin n) := insert j (A.erase i)

lemma mem_sw {A : Finset (Fin n)} {i j x : Fin n} : x ∈ sw A i j ↔ x = j ∨ (x ≠ i ∧ x ∈ A) := by
  simp [sw, mem_insert, mem_erase]

lemma card_sw {A : Finset (Fin n)} {k : ℕ} {i j : Fin n} (hA : A.card = k) (hi : i ∈ A)
    (hj : j ∉ A) : (sw A i j).card = k := by
  have h1 : j ∉ A.erase i := fun h => hj (mem_of_mem_erase h)
  rw [sw, card_insert_of_notMem h1, card_erase_of_mem hi]
  have := card_pos.mpr ⟨i, hi⟩
  omega

lemma card_compl_fin (s : Finset (Fin n)) : sᶜ.card = n - s.card := by
  rw [card_compl, Fintype.card_fin]

lemma exists_kset {k : ℕ} (s t : Finset (Fin n)) (hst : Disjoint s t) (hs : s.card ≤ k)
    (ht : k + t.card ≤ n) : ∃ A : Finset (Fin n), A.card = k ∧ s ⊆ A ∧ Disjoint A t := by
  obtain ⟨u, hsu, hut, hu⟩ := exists_subsuperset_card_eq (s := s) (t := tᶜ) (n := k)
    (by intro x hx; rw [mem_compl]; exact disjoint_left.mp hst hx) hs
    (by rw [card_compl_fin]; omega)
  exact ⟨u, hu, hsu, by rw [disjoint_left]; intro x hx; exact mem_compl.mp (hut hx)⟩

lemma sw_sw_back {A : Finset (Fin n)} {i j : Fin n} (hi : i ∈ A) (hj : j ∉ A) :
    sw (sw A i j) j i = A := by
  ext x; simp only [mem_sw]; grind

lemma sw_sw_trans {A : Finset (Fin n)} {i j l : Fin n} (hj : j ∉ A) :
    sw (sw A i j) j l = sw A i l := by
  ext x; simp only [mem_sw]; grind

lemma sw_sw_comm {A : Finset (Fin n)} {i i' j j' : Fin n} (h1 : i' ≠ j) (h2 : i' ≠ j') :
    sw (sw A i j) i' j' = sw (sw A i j') i' j := by
  ext x; simp only [mem_sw]; grind


/-! ### Swap identities for `f₁` -/

section Swaps

variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}

/-- Step 1: the swap identity. -/
lemma swap_id
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A C : Finset (Fin (3 * k))} (hA : A.card = k) (hC : C.card = k) (hAC : Disjoint A C)
    {i j : Fin (3 * k)} (hi : i ∈ A) (hj : j ∈ C) :
    f₁ (sw A i j) * (f₁ A)⁻¹ = (f₃ (sw C j i))⁻¹ * f₃ C := by
  have hij : i ≠ j := fun h => disjoint_left.mp hAC hi (h ▸ hj)
  have hjA : j ∉ A := fun h => disjoint_left.mp hAC h hj
  have hiC : i ∉ C := fun h => disjoint_left.mp hAC hi h
  set B := (A ∪ C)ᶜ with hB
  have hBc : B.card = k := by rw [hB, card_compl_fin, card_union_of_disjoint hAC]; omega
  have hAB : Disjoint A B := by
    rw [disjoint_left]; intro x hx hxB; simp [hB] at hxB; exact hxB.1 hx
  have hBC : Disjoint B C := by
    rw [disjoint_left]; intro x hxB hx; simp [hB] at hxB; exact hxB.2 hx
  have h1 := hP A B C hA hBc hC hAB hAC hBC
  have hA'B : Disjoint (sw A i j) B := by
    rw [disjoint_left]; intro x hx hxB; simp [hB] at hxB
    rcases mem_sw.mp hx with rfl | ⟨_, h⟩
    · exact hxB.2 hj
    · exact hxB.1 h
  have hBC' : Disjoint B (sw C j i) := by
    rw [disjoint_left]; intro x hxB hx; simp [hB] at hxB
    rcases mem_sw.mp hx with rfl | ⟨_, h⟩
    · exact hxB.1 hi
    · exact hxB.2 h
  have hA'C' : Disjoint (sw A i j) (sw C j i) := by
    rw [disjoint_left]; intro x hx hx'
    rcases mem_sw.mp hx with rfl | ⟨h1, h2⟩ <;> rcases mem_sw.mp hx' with h3 | ⟨h3, h4⟩
    · exact hij h3.symm
    · exact h3 rfl
    · exact h1 h3
    · exact disjoint_left.mp hAC h2 h4
  have h2 := hP (sw A i j) B (sw C j i) (card_sw hA hi hjA) hBc (card_sw hC hj hiC) hA'B hA'C' hBC'
  have e1 : f₂ B = (f₁ A)⁻¹ * (f₃ C)⁻¹ := by
    calc f₂ B = (f₁ A)⁻¹ * (f₁ A * f₂ B * f₃ C) * (f₃ C)⁻¹ := by group
      _ = _ := by rw [h1]; group
  rw [e1] at h2
  calc f₁ (sw A i j) * (f₁ A)⁻¹
      = (f₁ (sw A i j) * ((f₁ A)⁻¹ * (f₃ C)⁻¹) * f₃ (sw C j i)) * (f₃ (sw C j i))⁻¹ * f₃ C := by
        group
    _ = (f₃ (sw C j i))⁻¹ * f₃ C := by rw [h2]; group

/-- Step 2: independence of the swap ratio from the base set. -/
lemma indep (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A A' : Finset (Fin (3 * k))} (hA : A.card = k) (hA' : A'.card = k) {i j : Fin (3 * k)}
    (hi : i ∈ A) (hi' : i ∈ A') (hj : j ∉ A) (hj' : j ∉ A') :
    f₁ (sw A i j) * (f₁ A)⁻¹ = f₁ (sw A' i j) * (f₁ A')⁻¹ := by
  obtain ⟨C, hC, hjC, hCd⟩ := exists_kset (k := k) {j} (A ∪ A') (by simp [hj, hj']) (by rw [card_singleton]; omega)
    (by have := card_union_le A A'; omega)
  have hjC' : j ∈ C := hjC (mem_singleton_self j)
  rw [swap_id hP hA hC (hCd.symm.mono_left subset_union_left) hi hjC',
    swap_id hP hA' hC (hCd.symm.mono_left subset_union_right) hi' hjC']

/-- The swap ratio `δ(i, j)`. -/
noncomputable def dl (k : ℕ) (f₁ : Finset (Fin (3 * k)) → G) (i j : Fin (3 * k)) : G :=
  if h : ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A then
    f₁ (sw h.choose i j) * (f₁ h.choose)⁻¹ else 1

lemma dl_spec (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    (A : Finset (Fin (3 * k))) (hA : A.card = k) (i j : Fin (3 * k)) (hi : i ∈ A) (hj : j ∉ A) :
    f₁ (sw A i j) = dl k f₁ i j * f₁ A := by
  have h : ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A := ⟨A, hA, hi, hj⟩
  have hc := h.choose_spec
  simp only [dl, h, ↓reduceDIte]
  rw [ ← indep hk hP hA hc.1 hi hc.2.1 hj hc.2.2]
  group

/-- Swap rule for `f₃`. -/
lemma f3_swap (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    (C : Finset (Fin (3 * k))) (hC : C.card = k) (j i : Fin (3 * k)) (hj : j ∈ C) (hi : i ∉ C) :
    f₃ (sw C j i) = f₃ C * (dl k f₁ i j)⁻¹ := by
  obtain ⟨A, hA, hiA, hAC⟩ := exists_kset (k := k) {i} C (by simp [hi]) (by rw [card_singleton]; omega) (by omega)
  have hi' : i ∈ A := hiA (mem_singleton_self i)
  have hjA : j ∉ A := fun h => disjoint_left.mp hAC h hj
  have e := swap_id hP hA hC hAC hi' hj
  rw [dl_spec hk hP A hA i j hi' hjA] at e
  have e' : dl k f₁ i j = (f₃ (sw C j i))⁻¹ * f₃ C := by rw [← e]; group
  rw [e']; group

end Swaps

/-! ### Algebra of the swap ratios -/

section Delta

variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}

lemma ex1 (hk : 2 ≤ k) {i j : Fin (3 * k)} (hij : i ≠ j) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i} {j} (by simpa using hij) (by simp; omega)
    (by simp; omega)
  exact ⟨A, hA, hs (by simp), disjoint_right.mp ht (by simp)⟩

lemma ex2 (hk : 2 ≤ k) {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A ∧ l ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i} {j, l} (by simp [hij, hil]) (by simp; omega)
    (by rw [card_pair hjl]; omega)
  exact ⟨A, hA, hs (by simp), disjoint_right.mp ht (by simp), disjoint_right.mp ht (by simp)⟩

lemma ex4 (hk : 2 ≤ k) {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ i' ∈ A ∧ j ∉ A ∧ j' ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i, i'} {j, j'} (by simp [h2.symm, h3.symm, h4.symm, h5.symm])
    (by rw [card_pair h1]; omega) (by rw [card_pair h6]; omega)
  exact ⟨A, hA, hs (by simp), hs (by simp), disjoint_right.mp ht (by simp),
    disjoint_right.mp ht (by simp)⟩

variable (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs

/-- Step 3. -/
lemma d_inv {i j : Fin (3 * k)} (hij : i ≠ j) : d j i * d i j = 1 := by
  obtain ⟨A, hA, hi, hj⟩ := ex1 hk hij
  have h2 := hs (sw A i j) (card_sw hA hi hj) j i (mem_sw.mpr (Or.inl rfl))
    (by rw [mem_sw]; rintro (h | ⟨h, _⟩); exact hij h; exact h rfl)
  rw [sw_sw_back hi hj, hs A hA i j hi hj] at h2
  calc d j i * d i j = (d j i * (d i j * F A)) * (F A)⁻¹ := by group
    _ = 1 := by rw [← h2]; group

/-- Step 4: cocycle. -/
lemma d_cocycle {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    d i l = d j l * d i j := by
  obtain ⟨A, hA, hi, hj, hl⟩ := ex2 hk hij hil hjl
  have h2 := hs (sw A i j) (card_sw hA hi hj) j l (mem_sw.mpr (Or.inl rfl))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact hjl h.symm; exact hl h)
  rw [sw_sw_trans hj, hs A hA i l hi hl, hs A hA i j hi hj, ← mul_assoc] at h2
  exact mul_right_cancel h2

/-- Step 5: two-swap. -/
lemma d_two {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    d i' j' * d i j = d i' j * d i j' := by
  obtain ⟨A, hA, hi, hi', hj, hj'⟩ := ex4 hk h1 h2 h3 h4 h5 h6
  have e1 := hs (sw A i j) (card_sw hA hi hj) i' j' (mem_sw.mpr (Or.inr ⟨h1.symm, hi'⟩))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact h6 h.symm; exact hj' h)
  have e2 := hs (sw A i j') (card_sw hA hi hj') i' j (mem_sw.mpr (Or.inr ⟨h1.symm, hi'⟩))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact h6 h; exact hj h)
  rw [sw_sw_comm h4 h5, e2, hs A hA i j hi hj, hs A hA i j' hi hj', ← mul_assoc,
    ← mul_assoc] at e1
  exact mul_right_cancel e1.symm

/-- Step 6: shared-index commutation. -/
lemma d_comm {a b c : Fin (3 * k)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Commute (d a b) (d b c) := by
  obtain ⟨i, hi⟩ : ({a, b, c} : Finset (Fin (3 * k)))ᶜ.Nonempty := by
    rw [← card_pos, card_compl_fin]
    have := card_le_three (a := a) (b := b) (c := c)
    omega
  simp only [mem_compl, mem_insert, mem_singleton, not_or] at hi
  obtain ⟨hia, hib, hic⟩ := hi
  have h5 := d_two hk hs (i := i) (i' := a) (j := c) (j' := b) hia hic hib hac hab hbc.symm
  rw [d_cocycle hk hs hab hac hbc, d_cocycle hk hs hic hib hbc.symm] at h5
  have h3 := d_inv hk hs hbc
  have e : d a b = d b c * d a b * d c b := by
    have : d a b * d i c = (d b c * d a b * d c b) * d i c := by rw [h5]; group
    exact mul_right_cancel this
  show d a b * d b c = d b c * d a b
  nth_rewrite 1 [e]
  calc d b c * d a b * d c b * d b c = d b c * d a b * (d c b * d b c) := by group
    _ = d b c * d a b := by rw [h3, mul_one]

end Delta

/-! ### The generators `g` -/

section Gen

variable {G : Type*} [Group G] {k : ℕ}

/-- `g i = δ(o, i)` (and `g o = 1`). -/
def gg (d : Fin (3 * k) → Fin (3 * k) → G) (o i : Fin (3 * k)) : G := if i = o then 1 else d o i

variable {F : Finset (Fin (3 * k)) → G} {d : Fin (3 * k) → Fin (3 * k) → G} (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs

lemma gg_rel (o : Fin (3 * k)) {i j : Fin (3 * k)} (hij : i ≠ j) :
    d i j = gg d o j * (gg d o i)⁻¹ := by
  by_cases hi : i = o
  · subst hi; simp [gg, Ne.symm hij]
  by_cases hj : j = o
  · subst hj; simp only [gg, hi, ite_true, ite_false, one_mul]
    exact eq_inv_of_mul_eq_one_right (d_inv hk hs hij)
  simp only [gg, hi, hj, ite_false]
  rw [d_cocycle hk hs (Ne.symm hi) (Ne.symm hj) hij]
  group

lemma gg_comm (o i j : Fin (3 * k)) : Commute (gg d o i) (gg d o j) := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  by_cases hi : i = o
  · subst hi; simp only [gg, ite_true]; exact Commute.one_left _
  by_cases hj : j = o
  · subst hj; simp only [gg, ite_true]; exact Commute.one_right _
  have e : gg d o j = d i j * gg d o i := by rw [gg_rel hk hs o hij]; group
  rw [e]
  refine Commute.mul_right ?_ (Commute.refl _)
  simp only [gg, hi, ite_false]
  exact d_comm hk hs (Ne.symm hi) (Ne.symm hj) hij

end Gen

/-- Connectivity: a function invariant under swaps is constant on `k`-sets. -/
lemma const_of_swap {X : Type*} {k : ℕ} (F : Finset (Fin n) → X)
    (h : ∀ A : Finset (Fin n), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = F A) :
    ∀ m, ∀ A A' : Finset (Fin n), A.card = k → A'.card = k → (A \ A').card = m → F A = F A' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A A' hA hA' hm
  by_cases hsub : A ⊆ A'
  · rw [eq_of_subset_of_card_le hsub (by omega)]
  · obtain ⟨j, hjA, hjA'⟩ := not_subset.mp hsub
    have hsub' : ¬ A' ⊆ A := fun h' =>
      hjA' (by rw [eq_of_subset_of_card_le h' (by omega)]; exact hjA)
    obtain ⟨i, hiA', hiA⟩ := not_subset.mp hsub'
    rw [← h A hA j i hjA hiA]
    refine ih _ ?_ (sw A j i) A' (card_sw hA hjA hiA) hA' rfl
    rw [← hm]
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · refine ⟨j, mem_sdiff.mpr ⟨hjA, hjA'⟩, ?_⟩
      intro hx; rw [mem_sdiff, mem_sw] at hx
      rcases hx.1 with h' | ⟨h', _⟩
      · exact hiA (h' ▸ hjA)
      · exact h' rfl
    · intro x hx; rw [mem_sdiff, mem_sw] at hx; rw [mem_sdiff]
      rcases hx with ⟨rfl | ⟨_, h'⟩, h''⟩
      · exact absurd hiA' h''
      · exact ⟨h', h''⟩

lemma prod_sw {H : Type*} [CommGroup H] (g' : Fin n → H) {A : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ A) (hj : j ∉ A) :
    ∏ x ∈ sw A i j, g' x = g' j * (g' i)⁻¹ * ∏ x ∈ A, g' x := by
  have h1 : j ∉ A.erase i := fun h => hj (mem_of_mem_erase h)
  rw [sw, prod_insert h1, ← mul_prod_erase A g' hi]
  group

lemma comm_id {H : Type*} [CommGroup H] (a b c d e : H) :
    a * b⁻¹ * c⁻¹ * d = a * e * d * (b * e * c)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

lemma prod_ind {H : Type*} [CommGroup H] (g' : Fin n → H) (S : Finset (Fin n)) :
    ∏ i, g' i ^ (if i ∈ S then (1 : ℤ) else 0) = ∏ i ∈ S, g' i := by
  have := prod_ite_mem univ S g'
  rw [univ_inter] at this
  rw [← this]
  apply prod_congr rfl
  intro i _
  split_ifs <;> simp

/-- Core of the argument, in a commutative group mapping to `G`. -/
lemma core {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin (3 * k) → H)
    (hs1 : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A →
      f₁ (sw A i j) = φ (g' j * (g' i)⁻¹) * f₁ A)
    (hs3 : ∀ C : Finset (Fin (3 * k)), C.card = k → ∀ j i, j ∈ C → i ∉ C →
      f₃ (sw C j i) = f₃ C * φ (g' i * (g' j)⁻¹))
    (A B C : Finset (Fin (3 * k))) (hA : A.card = k) (hB : B.card = k) (hC : C.card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ i, g' i ^ (mult A B C i - 1)) := by
  set P : Finset (Fin (3 * k)) → H := fun S => ∏ x ∈ S, g' x with hPdef
  have c1 := const_of_swap (k := k) (fun S => (φ (P S))⁻¹ * f₁ S) (by
    intro S hS i j hi hj
    simp only [hPdef]
    rw [prod_sw g' hi hj, hs1 S hS i j hi hj]
    simp only [map_mul, map_inv]
    group)
  have c3 := const_of_swap (k := k) (fun S => f₃ S * (φ (P S))⁻¹) (by
    intro S hS j i hj hi
    simp only [hPdef]
    rw [prod_sw g' hj hi, mul_comm _ (∏ x ∈ S, g' x), hs3 S hS j i hj hi]
    simp only [map_mul, map_inv]
    group)
  obtain ⟨A₀, hA₀, -, hA₀B⟩ := exists_kset (k := k) ∅ B (by simp) (by simp) (by omega)
  set C₀ := (A₀ ∪ B)ᶜ with hC₀
  have hC₀c : C₀.card = k := by
    rw [hC₀, card_compl_fin, card_union_of_disjoint hA₀B]; omega
  have hA₀C₀ : Disjoint A₀ C₀ := by
    rw [disjoint_left]; intro x hx hxC; simp [hC₀] at hxC; exact hxC.1 hx
  have hBC₀ : Disjoint B C₀ := by
    rw [disjoint_left]; intro x hx hxC; simp [hC₀] at hxC; exact hxC.2 hx
  have h0 := hP A₀ B C₀ hA₀ hB hC₀c hA₀B hA₀C₀ hBC₀
  have e1 : (φ (P A))⁻¹ * f₁ A = (φ (P A₀))⁻¹ * f₁ A₀ := c1 _ A A₀ hA hA₀ rfl
  have e3 : f₃ C * (φ (P C))⁻¹ = f₃ C₀ * (φ (P C₀))⁻¹ := c3 _ C C₀ hC hC₀c rfl
  have hf1 : f₁ A = φ (P A) * ((φ (P A₀))⁻¹ * f₁ A₀) := by rw [← e1]; group
  have hf3 : f₃ C = (f₃ C₀ * (φ (P C₀))⁻¹) * φ (P C) := by rw [← e3]; group
  have hf2 : f₂ B = (f₁ A₀)⁻¹ * (f₃ C₀)⁻¹ := by
    calc f₂ B = (f₁ A₀)⁻¹ * (f₁ A₀ * f₂ B * f₃ C₀) * (f₃ C₀)⁻¹ := by group
      _ = _ := by rw [h0]; group
  have hU : ∏ i, g' i = P A₀ * P B * P C₀ := by
    rw [← prod_compl_mul_prod (A₀ ∪ B), prod_union hA₀B, ← hC₀, mul_comm]
  have hR : ∏ i, g' i ^ (mult A B C i - 1) = P A * P B * P C * (∏ i, g' i)⁻¹ := by
    simp only [hPdef, mult, zpow_sub, zpow_add, zpow_one, prod_mul_distrib, prod_inv_distrib, prod_ind]
  rw [hR, hU, ← comm_id, hf1, hf2, hf3]
  simp only [map_mul, map_inv]
  group

end Rig

/-- **Rigidity (non-abelian).** Let `k ≥ 2`. Suppose `f₁ A * f₂ B * f₃ C = 1` whenever `A, B, C` are
pairwise disjoint `k`-subsets of `Fin (3k)`. Then there are pairwise commuting `gᵢ` such that,
for every triple of `k`-subsets, `f₁ A * f₂ B * f₃ C = ∏ᵢ gᵢ ^ (mult A B C i - 1)`. -/
theorem rigidity {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C = psi g (fun i => mult A B C i - 1) := by
  have hs := Rig.dl_spec (f₂ := f₂) (f₃ := f₃) hk hP
  set d := Rig.dl k f₁ with hd
  let o : Fin (3 * k) := ⟨0, by omega⟩
  set g := Rig.gg d o with hg
  have hgc : ∀ i j, Commute (g i) (g j) := Rig.gg_comm hk hs o
  have hgr : ∀ i j, i ≠ j → d i j = g j * (g i)⁻¹ := fun i j hij => Rig.gg_rel hk hs o hij
  refine ⟨g, hgc, ?_⟩
  intro A B C hA hB hC
  let H := Subgroup.closure (Set.range g)
  have hcomm : (Set.range g).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hgc i j
  have hH : ∀ x y : H, x * y = y * x := fun x y =>
    (Subgroup.isMulCommutative_closure hcomm).is_comm.comm x y
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hH }
  let g' : Fin (3 * k) → H := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let φ : H →* G := H.subtype
  have hφ : ∀ i, φ (g' i) = g i := fun i => rfl
  have hs1 : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A →
      f₁ (Rig.sw A i j) = φ (g' j * (g' i)⁻¹) * f₁ A := by
    intro A hA i j hi hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [hs A hA i j hi hj, hgr i j hij, map_mul, map_inv, hφ, hφ]
  have hs3 : ∀ C : Finset (Fin (3 * k)), C.card = k → ∀ j i, j ∈ C → i ∉ C →
      f₃ (Rig.sw C j i) = f₃ C * φ (g' i * (g' j)⁻¹) := by
    intro C hC j i hj hi
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Rig.f3_swap (f₂ := f₂) hk hP C hC j i hj hi, ← hd, hgr i j hij, map_mul, map_inv, hφ, hφ,
      mul_inv_rev, inv_inv]
  rw [Rig.core hP φ g' hs1 hs3 A B C hA hB hC, psi, Fin.prod_univ_def, map_list_prod, List.map_map]
  congr 1

end SCCThm8
