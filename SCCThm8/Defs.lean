module

public import Mathlib

/-! Shared definitions for the Theorem 8 package. -/

@[expose] public section

namespace SCCThm8

open Finset

/-- Multiplicity of the point `i` in the triple `(A, B, C)`. -/
def mult {n : ℕ} (A B C : Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) + (if i ∈ C then 1 else 0)

/-- `psi g e = ∏ᵢ gᵢ ^ eᵢ`, taking the product in the order `0, 1, …, n-1`. -/
def psi {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) (e : Fin n → ℤ) : G :=
  ((List.finRange n).map fun i => g i ^ e i).prod

end SCCThm8
