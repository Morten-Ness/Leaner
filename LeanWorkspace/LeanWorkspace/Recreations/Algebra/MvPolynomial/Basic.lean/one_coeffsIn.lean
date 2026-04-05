import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

theorem one_coeffsIn : 1 ∈ MvPolynomial.coeffsIn σ M ↔ 1 ∈ M := by simpa using MvPolynomial.C_mem_coeffsIn (x := (1 : S))

