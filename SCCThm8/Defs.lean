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

/-- Multiplicity of the point `i` of block `j` in a triple of block-tuples. -/
def multP {m n : ℕ} (A B C : Fin m → Finset (Fin n)) (j : Fin m) (i : Fin n) : ℤ :=
  mult (A j) (B j) (C j) i

/-- `psiP g e = ∏_j ∏_i (g j i)^(e j i)`, taken in the order of the blocks `j` and then of `i`. -/
def psiP {G : Type*} [Group G] {m n : ℕ} (g : Fin m → Fin n → G) (e : Fin m → Fin n → ℤ) : G :=
  ((List.finRange m).map fun j => psi (g j) (e j)).prod

end SCCThm8
