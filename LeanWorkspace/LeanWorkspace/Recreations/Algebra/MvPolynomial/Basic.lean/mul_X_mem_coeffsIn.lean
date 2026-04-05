import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

theorem mul_X_mem_coeffsIn : p * MvPolynomial.X s ∈ MvPolynomial.coeffsIn σ M ↔ p ∈ MvPolynomial.coeffsIn σ M := by
  simpa [-MvPolynomial.mul_monomial_mem_coeffsIn] using MvPolynomial.mul_monomial_mem_coeffsIn (i := .single s 1)

