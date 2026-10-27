module

public import Mathlib

@[expose] public section

namespace SCCThm8

/-- Pratt's threshold `τ_k = 8^k · C(3k,k) · C(2k,k) / 27^k`. -/
noncomputable def tau (k : ℕ) : ℚ :=
  (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k

/-! ### Helper bounds for `tau_lt_two_pow` -/

/-- `C(n+1, ⌊(n+1)/2⌋)`-free step: `centralBinom (n+1) < 4 · centralBinom n`. -/
lemma centralBinom_succ_lt (n : ℕ) : Nat.centralBinom (n + 1) < 4 * Nat.centralBinom n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hpos := Nat.centralBinom_pos n
  have : (n + 1) * Nat.centralBinom (n + 1) < (n + 1) * (4 * Nat.centralBinom n) := by
    rw [h]; nlinarith
  exact Nat.lt_of_mul_lt_mul_left this

/-- `2 · C(2n,n) ≤ 4^n` for `n ≥ 1`. -/
lemma two_mul_centralBinom_le (n : ℕ) (hn : 1 ≤ n) : 2 * Nat.centralBinom n ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have := centralBinom_succ_lt n
    rw [pow_succ]; omega

/-- `2 · C(2k,k) < 4^k` for `k ≥ 2`. -/
lemma two_mul_choose_lt (k : ℕ) (hk : 2 ≤ k) : 2 * Nat.choose (2 * k) k < 4 ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 := centralBinom_succ_lt n
  have h2 := two_mul_centralBinom_le n (by omega)
  rw [← Nat.centralBinom_eq_two_mul_choose, pow_succ]
  omega

/-- Entropy bound `C(3k,k) · 4^k ≤ 27^k`, from one term of the binomial expansion of
`(k + 2k)^(3k)`. -/
lemma choose_three_mul_le (k : ℕ) : Nat.choose (3 * k) k * 4 ^ k ≤ 27 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hterm : k ^ k * (2 * k) ^ (3 * k - k) * Nat.choose (3 * k) k ≤ (k + 2 * k) ^ (3 * k) := by
    rw [add_pow]
    exact Finset.single_le_sum (f := fun m => k ^ m * (2 * k) ^ (3 * k - m) * (3 * k).choose m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  have e1 : k ^ k * (2 * k) ^ (3 * k - k) * Nat.choose (3 * k) k =
      k ^ (3 * k) * (Nat.choose (3 * k) k * 4 ^ k) := by
    rw [show 3 * k - k = 2 * k by omega, mul_pow, pow_mul, show 3 * k = k + 2 * k by ring,
      pow_add]
    norm_num; ring
  have e2 : (k + 2 * k) ^ (3 * k) = k ^ (3 * k) * 27 ^ k := by
    rw [show k + 2 * k = 3 * k by ring, mul_pow, pow_mul]; norm_num; ring
  rw [e1, e2] at hterm
  exact Nat.le_of_mul_le_mul_left hterm (by positivity)

/-- The group-restriction bound `2^(3k-1)` exceeds Pratt's threshold for every `k ≥ 2`. -/
theorem tau_lt_two_pow (k : ℕ) (hk : 2 ≤ k) : tau k < 2 ^ (3 * k - 1) := by
  have hnat : 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k < 27 ^ k := by
    have h1 := two_mul_choose_lt k hk
    have h2 := choose_three_mul_le k
    have hpos : 0 < Nat.choose (3 * k) k := Nat.choose_pos (by omega)
    calc 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k
        = Nat.choose (3 * k) k * (2 * Nat.choose (2 * k) k) := by ring
      _ < Nat.choose (3 * k) k * 4 ^ k := Nat.mul_lt_mul_of_pos_left h1 hpos
      _ ≤ 27 ^ k := h2
  have hq : (2 : ℚ) * Nat.choose (3 * k) k * Nat.choose (2 * k) k < 27 ^ k := by
    exact_mod_cast hnat
  have h8 : (8 : ℚ) ^ k = 2 ^ (3 * k - 1) * 2 := by
    rw [← pow_succ, show 3 * k - 1 + 1 = 3 * k by omega, pow_mul]; norm_num
  unfold tau
  rw [div_lt_iff₀ (by positivity), h8]
  have hp : (0 : ℚ) < 2 ^ (3 * k - 1) := by positivity
  calc (2 : ℚ) ^ (3 * k - 1) * 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k
      = 2 ^ (3 * k - 1) * (2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k) := by ring
    _ < 2 ^ (3 * k - 1) * 27 ^ k := mul_lt_mul_of_pos_left hq hp

/-! ### Helper identities for `tau_lt_central` -/

/-- The trinomial `C(3k,k) · C(2k,k) = (3k)! / (k!)^3`. -/
def trin (k : ℕ) : ℕ := Nat.choose (3 * k) k * Nat.choose (2 * k) k

lemma trin_mul_factorial (k : ℕ) : trin k * (k.factorial) ^ 3 = (3 * k).factorial := by
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (2 * k) k
  have h2 := Nat.add_choose_mul_factorial_mul_factorial k k
  rw [show 2 * k + k = 3 * k by ring] at h1
  rw [show k + k = 2 * k by ring] at h2
  unfold trin
  rw [← h1, ← h2]; ring

lemma trin_succ (k : ℕ) :
    (k + 1) ^ 2 * trin (k + 1) = 3 * (3 * k + 2) * (3 * k + 1) * trin k := by
  have h0 := trin_mul_factorial k
  have h1 := trin_mul_factorial (k + 1)
  have e1 : (3 * (k + 1)).factorial = (3 * k + 3) * ((3 * k + 2) * ((3 * k + 1) *
      (3 * k).factorial)) := by
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ (3 * k + 2),
      Nat.factorial_succ (3 * k + 1), Nat.factorial_succ (3 * k)]
  have e2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  rw [e1, e2, ← h0] at h1
  have hf : 0 < (k + 1) * (k.factorial) ^ 3 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hf
  calc (k + 1) ^ 2 * trin (k + 1) * ((k + 1) * k.factorial ^ 3)
      = trin (k + 1) * ((k + 1) * k.factorial) ^ 3 := by ring
    _ = (3 * k + 3) * ((3 * k + 2) * ((3 * k + 1) * (trin k * k.factorial ^ 3))) := h1
    _ = 3 * (3 * k + 2) * (3 * k + 1) * trin k * ((k + 1) * k.factorial ^ 3) := by ring

/-- `C(2m+1, m) · (m+1) = (2m+1) · C(2m, m)`. -/
lemma choose_odd_step (m : ℕ) :
    Nat.choose (2 * m + 1) m * (m + 1) = (2 * m + 1) * Nat.choose (2 * m) m := by
  have h := Nat.choose_mul_succ_eq (2 * m) m
  rw [show 2 * m + 1 - m = m + 1 by omega] at h
  rw [← h]; ring

/-- `C(2m+2, m+1) = 2 · C(2m+1, m)`. -/
lemma choose_even_step (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
  ring

/-- `c k = C(3k, ⌊3k/2⌋)`. -/
def cen (k : ℕ) : ℕ := Nat.choose (3 * k) (3 * k / 2)

lemma cen_pos (k : ℕ) : 0 < cen k := Nat.choose_pos (by omega)

lemma cen_step_even (j : ℕ) :
    (3 * j + 1) * (3 * j + 2) * cen (2 * j + 1) = 2 * (6 * j + 1) * (6 * j + 3) * cen (2 * j) := by
  unfold cen
  rw [show 3 * (2 * j + 1) = 2 * (3 * j + 1) + 1 by ring,
    show (2 * (3 * j + 1) + 1) / 2 = 3 * j + 1 by omega,
    show 3 * (2 * j) = 2 * (3 * j) by ring, show 2 * (3 * j) / 2 = 3 * j by omega]
  have a := choose_odd_step (3 * j)
  have b := choose_even_step (3 * j)
  have c := choose_odd_step (3 * j + 1)
  rw [show 2 * (3 * j) + 2 = 2 * (3 * j + 1) by ring] at b
  calc (3 * j + 1) * (3 * j + 2) * Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1)
      = (3 * j + 1) * (Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1) * (3 * j + 1 + 1)) := by ring
    _ = (3 * j + 1) * ((2 * (3 * j + 1) + 1) * (2 * Nat.choose (2 * (3 * j) + 1) (3 * j))) := by
        rw [c, b]
    _ = 2 * (2 * (3 * j + 1) + 1) * (Nat.choose (2 * (3 * j) + 1) (3 * j) * (3 * j + 1)) := by ring
    _ = 2 * (6 * j + 1) * (6 * j + 3) * Nat.choose (2 * (3 * j)) (3 * j) := by rw [a]; ring

lemma cen_step_odd (j : ℕ) :
    (3 * j + 3) * cen (2 * j + 1 + 1) = 4 * (6 * j + 5) * cen (2 * j + 1) := by
  unfold cen
  rw [show 3 * (2 * j + 1 + 1) = 2 * (3 * j + 2) + 2 by ring,
    show (2 * (3 * j + 2) + 2) / 2 = 3 * j + 2 + 1 by omega,
    show 3 * (2 * j + 1) = 2 * (3 * j + 1) + 1 by ring,
    show (2 * (3 * j + 1) + 1) / 2 = 3 * j + 1 by omega]
  have a := choose_even_step (3 * j + 1)
  have b := choose_odd_step (3 * j + 2)
  have c := choose_even_step (3 * j + 2)
  rw [show 2 * (3 * j + 1) + 2 = 2 * (3 * j + 2) by ring,
    show 3 * j + 1 + 1 = 3 * j + 2 by ring] at a
  calc (3 * j + 3) * Nat.choose (2 * (3 * j + 2) + 2) (3 * j + 2 + 1)
      = 2 * (Nat.choose (2 * (3 * j + 2) + 1) (3 * j + 2) * (3 * j + 2 + 1)) := by rw [c]; ring
    _ = 2 * ((2 * (3 * j + 2) + 1) * Nat.choose (2 * (3 * j + 2)) (3 * j + 2)) := by rw [b]
    _ = 4 * (6 * j + 5) * Nat.choose (2 * (3 * j + 1) + 1) (3 * j + 1) := by rw [a]; ring

/-- Monotonicity of `C(3k,⌊3k/2⌋) · 27^k / (8^k · trin k)`, in cross-multiplied form. -/
lemma ratio_step (k : ℕ) : 8 * trin (k + 1) * cen k ≤ 27 * cen (k + 1) * trin k := by
  have ht := trin_succ k
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hc := cen_step_even j
    set a1 := trin (2 * j + 1)
    set a0 := trin (2 * j)
    set c1 := cen (2 * j + 1)
    set c0 := cen (2 * j)
    have hX : 0 < (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) := by positivity
    apply Nat.le_of_mul_le_mul_left _ hX
    have eL : (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (8 * a1 * c0)
        = 24 * (6 * j + 2) * (6 * j + 1) * ((3 * j + 1) * (3 * j + 2)) * (a0 * c0) := by
      rw [show (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (8 * a1 * c0)
          = 8 * ((3 * j + 1) * (3 * j + 2)) * c0 * ((2 * j + 1) ^ 2 * a1) by ring, ht]
      ring
    have eR : (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (27 * c1 * a0)
        = 54 * (2 * j + 1) ^ 2 * (6 * j + 1) * (6 * j + 3) * (a0 * c0) := by
      rw [show (2 * j + 1) ^ 2 * ((3 * j + 1) * (3 * j + 2)) * (27 * c1 * a0)
          = 27 * (2 * j + 1) ^ 2 * a0 * ((3 * j + 1) * (3 * j + 2) * c1) by ring, hc]
      ring
    rw [eL, eR]
    apply Nat.mul_le_mul_right
    ring_nf; nlinarith
  · have hc := cen_step_odd j
    set a1 := trin (2 * j + 1 + 1)
    set a0 := trin (2 * j + 1)
    set c1 := cen (2 * j + 1 + 1)
    set c0 := cen (2 * j + 1)
    have hX : 0 < (2 * j + 1 + 1) ^ 2 * (3 * j + 3) := by positivity
    apply Nat.le_of_mul_le_mul_left _ hX
    have eL : (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (8 * a1 * c0)
        = 24 * (6 * j + 5) * (6 * j + 4) * (3 * j + 3) * (a0 * c0) := by
      rw [show (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (8 * a1 * c0)
          = 8 * (3 * j + 3) * c0 * ((2 * j + 1 + 1) ^ 2 * a1) by ring, ht]
      ring
    have eR : (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (27 * c1 * a0)
        = 108 * (2 * j + 1 + 1) ^ 2 * (6 * j + 5) * (a0 * c0) := by
      rw [show (2 * j + 1 + 1) ^ 2 * (3 * j + 3) * (27 * c1 * a0)
          = 27 * (2 * j + 1 + 1) ^ 2 * a0 * ((3 * j + 3) * c1) by ring, hc]
      ring
    rw [eL, eR]
    apply Nat.mul_le_mul_right
    ring_nf; nlinarith

lemma central_nat (k : ℕ) (hk : 1 ≤ k) : 8 ^ k * trin k < 27 ^ k * cen k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hs := ratio_step k
    have hc := cen_pos k
    apply Nat.lt_of_mul_lt_mul_right (a := cen k)
    calc 8 ^ (k + 1) * trin (k + 1) * cen k = 8 ^ k * (8 * trin (k + 1) * cen k) := by ring
      _ ≤ 8 ^ k * (27 * cen (k + 1) * trin k) := Nat.mul_le_mul_left _ hs
      _ = 27 * cen (k + 1) * (8 ^ k * trin k) := by ring
      _ < 27 * cen (k + 1) * (27 ^ k * cen k) :=
          Nat.mul_lt_mul_of_pos_left ih (by have := cen_pos (k + 1); positivity)
      _ = 27 ^ (k + 1) * cen (k + 1) * cen k := by ring

/-- Stretch goal: the group-degeneration bound `C(3k, ⌊3k/2⌋)` exceeds Pratt's threshold for every
`k ≥ 1`. -/
theorem tau_lt_central (k : ℕ) (hk : 1 ≤ k) : tau k < Nat.choose (3 * k) (3 * k / 2) := by
  have h := central_nat k hk
  unfold trin cen at h
  have hq : (8 : ℚ) ^ k * (Nat.choose (3 * k) k * Nat.choose (2 * k) k)
      < 27 ^ k * Nat.choose (3 * k) (3 * k / 2) := by exact_mod_cast h
  unfold tau
  rw [div_lt_iff₀ (by positivity)]
  linarith

end SCCThm8
