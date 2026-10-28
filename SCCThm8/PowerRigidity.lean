module

public import SCCThm8.Defs
public import SCCThm8.Rigidity

@[expose] public section

namespace SCCThm8

open Finset

namespace PRig

open Rig Function

/-- Connectivity for tuples: a function invariant under blockwise swaps is constant on tuples
of `k`-sets. -/
lemma constP {n m k : ℕ} {X : Type*} (F : (Fin m → Finset (Fin n)) → X)
    (h : ∀ A : Fin m → Finset (Fin n), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j → t ∉ A j →
      F (update A j (sw (A j) s t)) = F A)
    (A A' : Fin m → Finset (Fin n)) (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) :
    F A = F A' := by
  have step : ∀ A : Fin m → Finset (Fin n), (∀ j, (A j).card = k) → ∀ j (Y : Finset (Fin n)),
      Y.card = k → F (update A j Y) = F A := by
    intro A hA j Y hY
    have := Rig.const_of_swap (k := k) (fun Y => F (update A j Y)) (by
      intro Z hZ s t hs ht
      have hv : ∀ j', (update A j Z j').card = k := by
        intro j'; rcases eq_or_ne j' j with rfl | h' <;> simp [*]
      have := h (update A j Z) hv j s t (by simpa using hs) (by simpa using ht)
      simpa using this) _ Y (A j) hY (hA j) rfl
    simpa using this
  let Ar : ℕ → Fin m → Finset (Fin n) := fun r j => if j.val < r then A' j else A j
  have hAr : ∀ r j, (Ar r j).card = k := by
    intro r j; simp only [Ar]; split_ifs <;> simp [*]
  have key : ∀ r, F (Ar r) = F A := by
    intro r
    induction r with
    | zero =>
      have e0 : Ar 0 = A := by funext j; simp [Ar]
      rw [e0]
    | succ r ih =>
      by_cases hr : r < m
      · have e : Ar (r + 1) = update (Ar r) ⟨r, hr⟩ (A' ⟨r, hr⟩) := by
          funext j
          rcases eq_or_ne j ⟨r, hr⟩ with rfl | h'
          · simp [Ar]
          · have : j.val ≠ r := fun h'' => h' (Fin.ext h'')
            simp only [Ar, update_of_ne h']
            split_ifs <;> first | rfl | omega
        rw [e, step _ (hAr r) _ _ (hA' _), ih]
      · have e : Ar (r + 1) = Ar r := by
          funext j
          have := j.isLt
          simp only [Ar]
          split_ifs <;> first | rfl | omega
        rw [e, ih]
  have e : Ar m = A' := by funext j; simp [Ar, j.isLt]
  rw [← key m, e]

lemma prodP_update {n m : ℕ} {H : Type*} [CommGroup H] (g' : Fin m → Fin n → H)
    (A : Fin m → Finset (Fin n)) (j : Fin m) (Y : Finset (Fin n)) :
    ∏ j', ∏ x ∈ update A j Y j', g' j' x =
      (∏ x ∈ Y, g' j x) * (∏ x ∈ A j, g' j x)⁻¹ * ∏ j', ∏ x ∈ A j', g' j' x := by
  rw [← mul_prod_erase univ (fun j' => ∏ x ∈ update A j Y j', g' j' x) (mem_univ j),
    ← mul_prod_erase univ (fun j' => ∏ x ∈ A j', g' j' x) (mem_univ j)]
  have : ∏ j' ∈ univ.erase j, ∏ x ∈ update A j Y j', g' j' x =
      ∏ j' ∈ univ.erase j, ∏ x ∈ A j', g' j' x := by
    apply prod_congr rfl
    intro j' hj'
    rw [update_of_ne (ne_of_mem_erase hj')]
  simp only [update_self]
  rw [this]
  group

section Swaps

variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}

/-- The blockwise partition hypothesis. -/
def Good (k : ℕ) (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) : Prop :=
  ∀ A B C : Fin m → Finset (Fin (3 * k)),
    (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
    (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
    f₁ A * f₂ B * f₃ C = 1

lemma ctx (hP : Good k f₁ f₂ f₃) {A B C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k)
    (hD : ∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) (j : Fin m) :
    ∀ X Y Z : Finset (Fin (3 * k)), X.card = k → Y.card = k → Z.card = k →
      Disjoint X Y → Disjoint X Z → Disjoint Y Z →
      f₁ (update A j X) * f₂ (update B j Y) * f₃ (update C j Z) = 1 := by
  intro X Y Z hX hY hZ h1 h2 h3
  apply hP
  · intro j'; by_cases h : j' = j
    · subst h; simp [hX]
    · simp [h, hA]
  · intro j'; by_cases h : j' = j
    · subst h; simp [hY]
    · simp [h, hB]
  · intro j'; by_cases h : j' = j
    · subst h; simp [hZ]
    · simp [h, hC]
  · intro j'; rcases eq_or_ne j' j with rfl | h
    · simpa using ⟨h1, h2, h3⟩
    · simpa [h] using hD j'

/-- Swap identity for tuples. -/
lemma swap_idP (hP : Good k f₁ f₂ f₃) {A C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hC : ∀ j, (C j).card = k) (hAC : ∀ j, Disjoint (A j) (C j))
    {j : Fin m} {s t : Fin (3 * k)} (hs : s ∈ A j) (ht : t ∈ C j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = (f₃ (update C j (sw (C j) t s)))⁻¹ * f₃ C := by
  let B : Fin m → Finset (Fin (3 * k)) := fun j => (A j ∪ C j)ᶜ
  have hB : ∀ j, (B j).card = k := fun j => by
    simp only [B]; rw [card_compl_fin, card_union_of_disjoint (hAC j), hA j, hC j]; omega
  have hD : ∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j) := by
    intro j
    refine ⟨?_, hAC j, ?_⟩
    · rw [disjoint_left]; intro x hx hxB; simp [B] at hxB; exact hxB.1 hx
    · rw [disjoint_left]; intro x hxB hx; simp [B] at hxB; exact hxB.2 hx
  have := Rig.swap_id (f₁ := fun X => f₁ (update A j X)) (f₂ := fun Y => f₂ (update B j Y))
    (f₃ := fun Z => f₃ (update C j Z)) (ctx hP hA hB hC hD j) (hA j) (hC j) (hAC j) hs ht
  simpa only [update_eq_self] using this

/-- Independence of the swap ratio from the whole tuple. -/
lemma indepP (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {A A' : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) {j : Fin m} {s t : Fin (3 * k)}
    (hs : s ∈ A j) (hs' : s ∈ A' j) (ht : t ∉ A j) (ht' : t ∉ A' j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = f₁ (update A' j (sw (A' j) s t)) * (f₁ A')⁻¹ := by
  have hex : ∀ j', ∃ C : Finset (Fin (3 * k)), C.card = k ∧
      (if j' = j then {t} else ∅) ⊆ C ∧ Disjoint C (A j' ∪ A' j') := by
    intro j'
    refine exists_kset _ _ ?_ ?_ ?_
    · split_ifs with h
      · subst h; simp [ht, ht']
      · simp
    · split_ifs <;> simp; omega
    · have := card_union_le (A j') (A' j'); rw [hA j', hA' j'] at this; omega
  choose C hC hsub hdisj using hex
  have htC : t ∈ C j := hsub j (by simp)
  rw [swap_idP hP hA hC (fun j' => (hdisj j').symm.mono_left subset_union_left) hs htC,
    swap_idP hP hA' hC (fun j' => (hdisj j').symm.mono_left subset_union_right) hs' htC]

/-- The swap ratio `δ_j(s, t)`. -/
noncomputable def D (k : ℕ) (f₁ : (Fin m → Finset (Fin (3 * k))) → G) (j : Fin m)
    (s t : Fin (3 * k)) : G :=
  if h : ∃ A : Fin m → Finset (Fin (3 * k)), (∀ j', (A j').card = k) ∧ s ∈ A j ∧ t ∉ A j then
    f₁ (update h.choose j (sw (h.choose j) s t)) * (f₁ h.choose)⁻¹ else 1

lemma D_spec (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A : Fin m → Finset (Fin (3 * k)))
    (hA : ∀ j, (A j).card = k) (j : Fin m) (s t : Fin (3 * k)) (hs : s ∈ A j) (ht : t ∉ A j) :
    f₁ (update A j (sw (A j) s t)) = D k f₁ j s t * f₁ A := by
  have h : ∃ A : Fin m → Finset (Fin (3 * k)), (∀ j', (A j').card = k) ∧ s ∈ A j ∧ t ∉ A j :=
    ⟨A, hA, hs, ht⟩
  have hc := h.choose_spec
  simp only [D, h, ↓reduceDIte]
  rw [← indepP hk hP hA hc.1 hs hc.2.1 ht hc.2.2]
  group

lemma f3_swapP (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (C : Fin m → Finset (Fin (3 * k)))
    (hC : ∀ j, (C j).card = k) (j : Fin m) (t s : Fin (3 * k)) (ht : t ∈ C j) (hs : s ∉ C j) :
    f₃ (update C j (sw (C j) t s)) = f₃ C * (D k f₁ j s t)⁻¹ := by
  have hex : ∀ j', ∃ A : Finset (Fin (3 * k)), A.card = k ∧
      (if j' = j then {s} else ∅) ⊆ A ∧ Disjoint A (C j') := by
    intro j'
    refine exists_kset _ _ ?_ ?_ ?_
    · split_ifs with h
      · subst h; simp [hs]
      · simp
    · split_ifs <;> simp; omega
    · rw [hC j']; omega
  choose A hA hsub hdisj using hex
  have hsA : s ∈ A j := hsub j (by simp)
  have htA : t ∉ A j := fun h => disjoint_left.mp (hdisj j) h ht
  have e := swap_idP hP hA hC hdisj hsA ht
  rw [D_spec hk hP A hA j s t hsA htA] at e
  have e' : D k f₁ j s t = (f₃ (update C j (sw (C j) t s)))⁻¹ * f₃ C := by rw [← e]; group
  rw [e']; group

lemma blk (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A₀ : Fin m → Finset (Fin (3 * k)))
    (hA₀ : ∀ j, (A₀ j).card = k) (j : Fin m) :
    ∀ X : Finset (Fin (3 * k)), X.card = k → ∀ s t, s ∈ X → t ∉ X →
      f₁ (update A₀ j (sw X s t)) = D k f₁ j s t * f₁ (update A₀ j X) := by
  intro X hX s t hs ht
  have hv : ∀ j', (update A₀ j X j').card = k := by
    intro j'; rcases eq_or_ne j' j with rfl | h' <;> simp [*]
  have := D_spec hk hP (update A₀ j X) hv j s t (by simpa using hs) (by simpa using ht)
  simpa using this

lemma D_cross (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {j j' : Fin m} (hjj : j ≠ j')
    {s t s' t' : Fin (3 * k)} (hst : s ≠ t) (hst' : s' ≠ t') :
    D k f₁ j s t * D k f₁ j' s' t' = D k f₁ j' s' t' * D k f₁ j s t := by
  obtain ⟨X, hX, hsX, htX⟩ := Rig.ex1 hk hst
  obtain ⟨Y, hY, hsY, htY⟩ := Rig.ex1 hk hst'
  let A : Fin m → Finset (Fin (3 * k)) := update (fun _ => X) j' Y
  have hAj : A j = X := by simp [A, hjj]
  have hAj' : A j' = Y := by simp [A]
  have hA : ∀ i, (A i).card = k := by
    intro i; rcases eq_or_ne i j' with rfl | h <;> simp [A, *]
  let A1 := update A j (sw X s t)
  let A2 := update A j' (sw Y s' t')
  have hA1 : ∀ i, (A1 i).card = k := by
    intro i; rcases eq_or_ne i j with rfl | h
    · simp [A1, card_sw hX hsX htX]
    · simp [A1, h, hA]
  have hA2 : ∀ i, (A2 i).card = k := by
    intro i; rcases eq_or_ne i j' with rfl | h
    · simp [A2, card_sw hY hsY htY]
    · simp [A2, h, hA]
  have hA1j' : A1 j' = Y := by simp [A1, hjj.symm, hAj']
  have hA2j : A2 j = X := by simp [A2, hjj, hAj]
  have e1 := D_spec hk hP A hA j s t (hAj ▸ hsX) (hAj ▸ htX)
  have e2 := D_spec hk hP A hA j' s' t' (hAj' ▸ hsY) (hAj' ▸ htY)
  have e3 := D_spec hk hP A1 hA1 j' s' t' (hA1j' ▸ hsY) (hA1j' ▸ htY)
  have e4 := D_spec hk hP A2 hA2 j s t (hA2j ▸ hsX) (hA2j ▸ htX)
  rw [hAj] at e1
  rw [hAj'] at e2
  rw [hA1j'] at e3
  rw [hA2j] at e4
  have hcomm : update A1 j' (sw Y s' t') = update A2 j (sw X s t) := update_comm hjj _ _ _
  rw [hcomm, e4] at e3
  have e2' : f₁ A2 = D k f₁ j' s' t' * f₁ A := e2
  have e1' : f₁ A1 = D k f₁ j s t * f₁ A := e1
  rw [e2', e1', ← mul_assoc, ← mul_assoc] at e3
  exact mul_right_cancel e3

end Swaps

/-- Core of the argument, in a commutative group mapping to `G`. -/
lemma coreP {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
    (hP : Good k f₁ f₂ f₃)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin m → Fin (3 * k) → H)
    (hs1 : ∀ A : Fin m → Finset (Fin (3 * k)), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j →
      t ∉ A j → f₁ (update A j (sw (A j) s t)) = φ (g' j t * (g' j s)⁻¹) * f₁ A)
    (hs3 : ∀ C : Fin m → Finset (Fin (3 * k)), (∀ j, (C j).card = k) → ∀ j t s, t ∈ C j →
      s ∉ C j → f₃ (update C j (sw (C j) t s)) = f₃ C * φ (g' j s * (g' j t)⁻¹))
    (A B C : Fin m → Finset (Fin (3 * k))) (hA : ∀ j, (A j).card = k)
    (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ j, ∏ i, g' j i ^ (multP A B C j i - 1)) := by
  set P : (Fin m → Finset (Fin (3 * k))) → H := fun S => ∏ j, ∏ x ∈ S j, g' j x with hPdef
  have c1 := constP (k := k) (fun S => (φ (P S))⁻¹ * f₁ S) (by
    intro S hS j s t hs ht
    simp only [hPdef]
    rw [prodP_update, prod_sw (g' j) hs ht, mul_inv_cancel_right, hs1 S hS j s t hs ht]
    simp only [map_mul, map_inv]
    group)
  have c3 := constP (k := k) (fun S => f₃ S * (φ (P S))⁻¹) (by
    intro S hS j t s ht hs
    simp only [hPdef]
    rw [prodP_update, prod_sw (g' j) ht hs, mul_inv_cancel_right, hs3 S hS j t s ht hs,
      mul_comm (g' j s * (g' j t)⁻¹)]
    simp only [map_mul, map_inv]
    group)
  have hex : ∀ j, ∃ X : Finset (Fin (3 * k)), X.card = k ∧ (∅ : Finset (Fin (3 * k))) ⊆ X ∧
      Disjoint X (B j) := fun j => exists_kset (k := k) ∅ (B j) (by simp) (by simp)
        (by rw [hB j]; omega)
  choose A₀ hA₀ _ hA₀B using hex
  let C₀ : Fin m → Finset (Fin (3 * k)) := fun j => (A₀ j ∪ B j)ᶜ
  have hC₀c : ∀ j, (C₀ j).card = k := fun j => by
    simp only [C₀]; rw [card_compl_fin, card_union_of_disjoint (hA₀B j), hA₀ j, hB j]; omega
  have hA₀C₀ : ∀ j, Disjoint (A₀ j) (C₀ j) := by
    intro j; rw [disjoint_left]; intro x hx hxC; simp [C₀] at hxC; exact hxC.1 hx
  have hBC₀ : ∀ j, Disjoint (B j) (C₀ j) := by
    intro j; rw [disjoint_left]; intro x hx hxC; simp [C₀] at hxC; exact hxC.2 hx
  have h0 := hP A₀ B C₀ hA₀ hB hC₀c (fun j => ⟨hA₀B j, hA₀C₀ j, hBC₀ j⟩)
  have e1 : (φ (P A))⁻¹ * f₁ A = (φ (P A₀))⁻¹ * f₁ A₀ := c1 A A₀ hA hA₀
  have e3 : f₃ C * (φ (P C))⁻¹ = f₃ C₀ * (φ (P C₀))⁻¹ := c3 C C₀ hC hC₀c
  have hf1 : f₁ A = φ (P A) * ((φ (P A₀))⁻¹ * f₁ A₀) := by rw [← e1]; group
  have hf3 : f₃ C = (f₃ C₀ * (φ (P C₀))⁻¹) * φ (P C) := by rw [← e3]; group
  have hf2 : f₂ B = (f₁ A₀)⁻¹ * (f₃ C₀)⁻¹ := by
    calc f₂ B = (f₁ A₀)⁻¹ * (f₁ A₀ * f₂ B * f₃ C₀) * (f₃ C₀)⁻¹ := by group
      _ = _ := by rw [h0]; group
  have hU : ∏ j, ∏ i, g' j i = P A₀ * P B * P C₀ := by
    simp only [hPdef, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    rw [← prod_compl_mul_prod (A₀ j ∪ B j), prod_union (hA₀B j), mul_comm]
  have hR : ∏ j, ∏ i, g' j i ^ (multP A B C j i - 1) = P A * P B * P C * (∏ j, ∏ i, g' j i)⁻¹ := by
    simp only [hPdef, multP, mult, zpow_sub, zpow_add, zpow_one, prod_mul_distrib,
      prod_inv_distrib, prod_ind]
  rw [hR, hU, ← comm_id, hf1, hf2, hf3]
  simp only [map_mul, map_inv]
  group

end PRig

/-- **Block rigidity for `T_k^{⊗m}`.** Let `k ≥ 2`, and index the tensor power by `m`-tuples of
`k`-subsets of `Fin (3k)`. Suppose `f₁ A * f₂ B * f₃ C = 1` whenever `A j, B j, C j` are pairwise
disjoint in every block `j`. Then there are pairwise commuting `g j i` (over all blocks and points)
such that for every triple of tuples, `f₁ A * f₂ B * f₃ C = ∏_j ∏_i (g j i)^(multP A B C j i - 1)`. -/
theorem power_rigidity {G : Type*} [Group G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G)
    (hP : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
      f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin m → Fin (3 * k) → G, (∀ j i j' i', Commute (g j i) (g j' i')) ∧
      ∀ A B C : Fin m → Finset (Fin (3 * k)),
        (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
        f₁ A * f₂ B * f₃ C = psiP g (fun j i => multP A B C j i - 1) := by
  have hP' : PRig.Good k f₁ f₂ f₃ := hP
  set D := PRig.D k f₁ with hD
  obtain ⟨X₀, hX₀, -, -⟩ := Rig.exists_kset (k := k) (∅ : Finset (Fin (3 * k))) ∅ (by simp)
    (by simp) (by simp; omega)
  let A₀ : Fin m → Finset (Fin (3 * k)) := fun _ => X₀
  have hb := PRig.blk hk hP' A₀ (fun _ => hX₀)
  let o : Fin (3 * k) := ⟨0, by omega⟩
  let g : Fin m → Fin (3 * k) → G := fun j => Rig.gg (D j) o
  have hgr : ∀ j s t, s ≠ t → D j s t = g j t * (g j s)⁻¹ := fun j s t h =>
    Rig.gg_rel (F := fun X => f₁ (Function.update A₀ j X)) hk (hb j) o h
  have hgc : ∀ j i j' i', Commute (g j i) (g j' i') := by
    intro j i j' i'
    rcases eq_or_ne j j' with rfl | hjj
    · exact Rig.gg_comm (F := fun X => f₁ (Function.update A₀ j X)) hk (hb j) o i i'
    · simp only [g, Rig.gg]
      split_ifs with h1 h2 h2
      · exact Commute.one_left _
      · exact Commute.one_left _
      · exact Commute.one_right _
      · exact PRig.D_cross hk hP' hjj (Ne.symm h1) (Ne.symm h2)
  refine ⟨g, hgc, ?_⟩
  intro A B C hA hB hC
  let H := Subgroup.closure (Set.range fun p : Fin m × Fin (3 * k) => g p.1 p.2)
  have hcomm : (Set.range fun p : Fin m × Fin (3 * k) => g p.1 p.2).Pairwise Commute := by
    rintro _ ⟨⟨j, i⟩, rfl⟩ _ ⟨⟨j', i'⟩, rfl⟩ _; exact hgc j i j' i'
  have hH : ∀ x y : H, x * y = y * x := fun x y =>
    (Subgroup.isMulCommutative_closure hcomm).is_comm.comm x y
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hH }
  let g' : Fin m → Fin (3 * k) → H := fun j i => ⟨g j i, Subgroup.subset_closure ⟨(j, i), rfl⟩⟩
  let φ : H →* G := H.subtype
  have hφ : ∀ j i, φ (g' j i) = g j i := fun j i => rfl
  have hs1 : ∀ A : Fin m → Finset (Fin (3 * k)), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j →
      t ∉ A j → f₁ (Function.update A j (Rig.sw (A j) s t)) = φ (g' j t * (g' j s)⁻¹) * f₁ A := by
    intro A hA j s t hs ht
    have hst : s ≠ t := fun h => ht (h ▸ hs)
    rw [PRig.D_spec hk hP' A hA j s t hs ht, ← hD, hgr j s t hst, map_mul, map_inv, hφ, hφ]
  have hs3 : ∀ C : Fin m → Finset (Fin (3 * k)), (∀ j, (C j).card = k) → ∀ j t s, t ∈ C j →
      s ∉ C j → f₃ (Function.update C j (Rig.sw (C j) t s)) = f₃ C * φ (g' j s * (g' j t)⁻¹) := by
    intro C hC j t s ht hs
    have hst : s ≠ t := fun h => hs (h ▸ ht)
    rw [PRig.f3_swapP hk hP' C hC j t s ht hs, ← hD, hgr j s t hst, map_mul, map_inv, hφ, hφ,
      mul_inv_rev, inv_inv]
  rw [PRig.coreP hP' φ g' hs1 hs3 A B C hA hB hC, psiP, Fin.prod_univ_def, map_list_prod,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [psi, Fin.prod_univ_def, map_list_prod, List.map_map]
  rfl

end SCCThm8
