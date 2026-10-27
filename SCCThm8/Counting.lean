module

public import SCCThm8.Defs

@[expose] public section

namespace SCCThm8

open Finset

/-! ### Realizability -/

theorem mem_ite_insert {α : Type*} [DecidableEq α] (c : Prop) [Decidable c] (x i : α)
    (A : Finset α) : i ∈ (if c then insert x A else A) ↔ (c ∧ i = x) ∨ i ∈ A := by
  split_ifs with h <;> simp [h]

/-- Incremental round-robin dealing: for any finset `s` and multiplicities `m ≤ 3`, there are
subsets `A, B, C ⊆ s` of sizes `⌈N/3⌉, ⌈(N-1)/3⌉, ⌊N/3⌋` (where `N = ∑_{s} m`) realizing `m`. -/
theorem realize_aux {α : Type*} [DecidableEq α] (m : α → ℕ) (hm : ∀ i, m i ≤ 3)
    (s : Finset α) :
    ∃ A B C : Finset α, A ⊆ s ∧ B ⊆ s ∧ C ⊆ s ∧
      A.card = (∑ i ∈ s, m i + 2) / 3 ∧ B.card = (∑ i ∈ s, m i + 1) / 3 ∧
      C.card = (∑ i ∈ s, m i) / 3 ∧
      ∀ i ∈ s, (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
        (if i ∈ C then 1 else 0) = m i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, ∅, ∅, by simp⟩
  | insert x s hx ih =>
    obtain ⟨A, B, C, hA, hB, hC, cA, cB, cC, hmul⟩ := ih
    have ht := hm x
    have hxA : x ∉ A := fun h => hx (hA h)
    have hxB : x ∉ B := fun h => hx (hB h)
    have hxC : x ∉ C := fun h => hx (hC h)
    rw [sum_insert hx]
    set N := ∑ i ∈ s, m i
    refine ⟨if (m x + N + 2) / 3 ≠ (N + 2) / 3 then insert x A else A,
      if (m x + N + 1) / 3 ≠ (N + 1) / 3 then insert x B else B,
      if (m x + N) / 3 ≠ N / 3 then insert x C else C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact insert_subset_insert _ hA
      · exact hA.trans (subset_insert _ _)
    · split_ifs
      · exact insert_subset_insert _ hB
      · exact hB.trans (subset_insert _ _)
    · split_ifs
      · exact insert_subset_insert _ hC
      · exact hC.trans (subset_insert _ _)
    · split_ifs with h
      · rw [card_insert_of_notMem hxA]; omega
      · omega
    · split_ifs with h
      · rw [card_insert_of_notMem hxB]; omega
      · omega
    · split_ifs with h
      · rw [card_insert_of_notMem hxC]; omega
      · omega
    · intro i hi
      simp only [mem_ite_insert]
      rcases mem_insert.1 hi with rfl | hi
      · simp only [hxA, hxB, hxC, and_true, or_false]
        split_ifs <;> omega
      · have hix : i ≠ x := fun h => hx (h ▸ hi)
        simp only [hix, and_false, false_or]
        exact hmul i hi

/-- **Realizability (Lemma 2).** Every `m ∈ {0,1,2,3}^(3k)` with `∑ m = 3k` is the multiplicity
vector of some triple of `k`-subsets. -/
theorem realizable (k : ℕ) (m : Fin (3 * k) → ℤ) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 3)
    (hs : ∑ i, m i = 3 * k) :
    ∃ A B C : Finset (Fin (3 * k)), A.card = k ∧ B.card = k ∧ C.card = k ∧
      ∀ i, mult A B C i = m i := by
  obtain ⟨A, B, C, -, -, -, cA, cB, cC, hmul⟩ :=
    realize_aux (fun i => (m i).toNat) (fun i => by have := hm i; omega) univ
  have hsum : ∑ i, (m i).toNat = 3 * k := by
    have : ((∑ i, (m i).toNat : ℕ) : ℤ) = 3 * k := by
      rw [Nat.cast_sum, ← hs]
      exact sum_congr rfl fun i _ => by have := hm i; omega
    exact_mod_cast this
  rw [hsum] at cA cB cC
  refine ⟨A, B, C, by omega, by omega, by omega, fun i => ?_⟩
  have h1 := hmul i (mem_univ i)
  have h2 := hm i
  unfold mult
  split_ifs at h1 ⊢ <;> simp at h1 <;> omega

/-! ### Counting via the lift lemma -/

/-- Splitting a product of pointwise products, for commuting families. -/
theorem list_prod_map_mul_of_commute {G ι : Type*} [Group G] (l : List ι) (a b : ι → G)
    (h : ∀ i j, Commute (a i) (b j)) :
    (l.map fun i => a i * b i).prod = (l.map a).prod * (l.map b).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    have hx : Commute (b x) (l.map a).prod :=
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
        exact (h j x).symm)
    rw [mul_assoc, ← mul_assoc (b x), hx.eq]
    simp only [mul_assoc]

/-- For a commuting family, `psi g` is additive. -/
theorem psi_add {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j)) (e e' : Fin n → ℤ) :
    psi g (e + e') = psi g e * psi g e' := by
  unfold psi
  simp only [Pi.add_apply, zpow_add]
  exact list_prod_map_mul_of_commute _ (fun i => g i ^ e i) (fun i => g i ^ e' i)
    (fun i j => (hc i j).zpow_zpow _ _)

/-- Rank of `i` within `v`: the number of elements of `v` below `i`. -/
def cntRank {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : ℕ := (v.filter (· < i)).card

/-- The lift vector of `v`: `+1` on the first half of `v`, `-1` on the second half, `0` off `v`. -/
def cntLift {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : ℤ :=
  if i ∈ v then (if 2 * cntRank v i < v.card then 1 else -1) else 0

theorem sum_cntRank {n : ℕ} (f : ℕ → ℤ) (v : Finset (Fin n)) :
    ∑ i ∈ v, f (cntRank v i) = ∑ r ∈ range v.card, f r := by
  induction v using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [sum_insert has, card_insert_of_notMem has, sum_range_succ]
    have h1 : cntRank (insert a s) a = s.card := by
      unfold cntRank
      rw [filter_insert, ite_eq_right (lt_irrefl a), filter_true_of_mem ha]
    have h2 : ∀ i ∈ s, cntRank (insert a s) i = cntRank s i := by
      intro i hi
      unfold cntRank
      rw [filter_insert, ite_eq_right (not_lt.2 (ha i hi).le)]
    rw [h1, add_comm, ← ih]
    congr 1
    exact sum_congr rfl fun i hi => by rw [h2 i hi]

theorem sum_cntLift {n : ℕ} (v : Finset (Fin n)) (hv : Even v.card) :
    ∑ i, cntLift v i = 0 := by
  have h : ∑ i, cntLift v i =
      ∑ i ∈ v, (fun r => if 2 * r < v.card then (1 : ℤ) else -1) (cntRank v i) := by
    rw [← sum_subset (subset_univ v)]
    · exact sum_congr rfl fun i hi => by simp [cntLift, hi]
    · intro i _ hi
      simp [cntLift, hi]
  rw [h]
  refine (sum_cntRank (fun r => if 2 * r < v.card then (1 : ℤ) else -1) v).trans ?_
  obtain ⟨k, hk⟩ := hv
  rw [hk, sum_range_add]
  have e1 : ∑ x ∈ range k, (if 2 * x < k + k then (1 : ℤ) else -1) = ∑ x ∈ range k, (1 : ℤ) :=
    sum_congr rfl fun x hx => by rw [mem_range] at hx; rw [ite_eq_left (by omega)]
  have e2 : ∑ x ∈ range k, (if 2 * (k + x) < k + k then (1 : ℤ) else -1) =
      ∑ x ∈ range k, (-1 : ℤ) :=
    sum_congr rfl fun x _ => by rw [ite_eq_right (by omega)]
  rw [e1, e2]
  simp

theorem cntLift_bounds {n : ℕ} (v : Finset (Fin n)) (i : Fin n) :
    -1 ≤ cntLift v i ∧ cntLift v i ≤ 1 := by
  unfold cntLift
  split_ifs <;> norm_num

theorem cntLift_eq_one {n : ℕ} {v : Finset (Fin n)} {i : Fin n} (h : cntLift v i = 1) :
    i ∈ v ∧ 2 * cntRank v i < v.card := by
  unfold cntLift at h
  split_ifs at h with h1 h2 <;> simp_all

theorem cntLift_eq_neg_one {n : ℕ} {v : Finset (Fin n)} {i : Fin n} (h : cntLift v i = -1) :
    i ∈ v ∧ ¬ 2 * cntRank v i < v.card := by
  unfold cntLift at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩

theorem mem_iff_cntLift_ne {n : ℕ} (v : Finset (Fin n)) (i : Fin n) :
    i ∈ v ↔ cntLift v i ≠ 0 := by
  unfold cntLift
  split_ifs <;> simp_all

theorem cntRank_mono {n : ℕ} (v : Finset (Fin n)) {i j : Fin n} (h : i < j) :
    cntRank v i ≤ cntRank v j := by
  unfold cntRank
  exact card_le_card fun x hx => by
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

/-- The difference of two lift vectors never contains both a `+2` and a `-2`. -/
theorem cntLift_diff {n : ℕ} (v v' : Finset (Fin n)) :
    (∀ i, -1 ≤ cntLift v i - cntLift v' i) ∨ (∀ i, -1 ≤ cntLift v' i - cntLift v i) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le] at hcon
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := hcon
  have bj := cntLift_bounds v j
  have bj' := cntLift_bounds v' j
  have bi := cntLift_bounds v i
  have bi' := cntLift_bounds v' i
  obtain ⟨-, hvj2⟩ := cntLift_eq_neg_one (v := v) (i := j) (by omega)
  obtain ⟨-, hv'j2⟩ := cntLift_eq_one (v := v') (i := j) (by omega)
  obtain ⟨-, hvi2⟩ := cntLift_eq_one (v := v) (i := i) (by omega)
  obtain ⟨-, hv'i2⟩ := cntLift_eq_neg_one (v := v') (i := i) (by omega)
  rcases lt_trichotomy i j with hij | rfl | hji
  · have := cntRank_mono v' hij
    omega
  · omega
  · have := cntRank_mono v hji
    omega

/-- **Counting (Theorem 3, via the lift lemma).** Let the `gᵢ` commute pairwise, and suppose
`∏ gᵢ^eᵢ ≠ 1` for every nonzero `e ∈ {-1,0,1,2}^n` with `∑ e = 0`. Then `|G| ≥ 2^(n-1)`. -/
theorem card_bound {G : Type*} [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n) (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j))
    (hE : ∀ e : Fin n → ℤ, (∀ i, -1 ≤ e i ∧ e i ≤ 2) → ∑ i, e i = 0 → e ≠ 0 → psi g e ≠ 1) :
    2 ^ (n - 1) ≤ Fintype.card G := by
  -- one-sided injectivity step
  have aux : ∀ v v' : Finset (Fin n), Even v.card → Even v'.card →
      psi g (cntLift v) = psi g (cntLift v') → (∀ i, -1 ≤ cntLift v i - cntLift v' i) →
      v = v' := by
    intro v v' hv hv' hpsi hd
    by_contra hne
    obtain ⟨d, hd_def⟩ : ∃ d : Fin n → ℤ, d = fun i => cntLift v i - cntLift v' i := ⟨_, rfl⟩
    have hsplit : psi g (cntLift v) = psi g d * psi g (cntLift v') := by
      rw [← psi_add g hc]
      congr 1
      funext i
      simp [hd_def]
    rw [hsplit] at hpsi
    have hd1 : psi g d = 1 := by
      have := hpsi.trans (one_mul (psi g (cntLift v'))).symm
      exact mul_right_cancel this
    refine hE d (fun i => ?_) ?_ ?_ hd1
    · have := cntLift_bounds v i
      have := cntLift_bounds v' i
      have := hd i
      subst hd_def
      show -1 ≤ cntLift v i - cntLift v' i ∧ cntLift v i - cntLift v' i ≤ 2
      constructor <;> omega
    · subst hd_def
      rw [sum_sub_distrib, sum_cntLift v hv, sum_cntLift v' hv', sub_zero]
    · intro h0
      apply hne
      ext i
      have := congrFun h0 i
      subst hd_def
      simp only [Pi.zero_apply] at this
      rw [mem_iff_cntLift_ne, mem_iff_cntLift_ne]
      omega
  have key : ∀ v v' : Finset (Fin n), Even v.card → Even v'.card →
      psi g (cntLift v) = psi g (cntLift v') → v = v' := by
    intro v v' hv hv' hpsi
    rcases cntLift_diff v v' with h | h
    · exact aux v v' hv hv' hpsi h
    · exact (aux v' v hv' hv hpsi.symm h).symm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  let φ : Finset (Fin m) → Finset (Fin (m + 1)) := fun w =>
    if Even w.card then w.map Fin.castSuccEmb
    else insert (Fin.last m) (w.map Fin.castSuccEmb)
  have hφmem : ∀ w (i : Fin m), Fin.castSucc i ∈ φ w ↔ i ∈ w := by
    intro w i
    simp only [φ]
    split_ifs <;> simp [Fin.castSucc_ne_last]
  have hφinj : Function.Injective φ := fun w w' h => by
    ext i
    rw [← hφmem, h, hφmem]
  have hφeven : ∀ w, Even (φ w).card := by
    intro w
    simp only [φ]
    split_ifs with h
    · simpa using h
    · rw [card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), card_map]
      exact (Nat.not_even_iff_odd.1 h).add_one
  have hinj : Function.Injective (fun w => psi g (cntLift (φ w))) := fun w w' h =>
    hφinj (key _ _ (hφeven w) (hφeven w') h)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_finset] using this

end SCCThm8
