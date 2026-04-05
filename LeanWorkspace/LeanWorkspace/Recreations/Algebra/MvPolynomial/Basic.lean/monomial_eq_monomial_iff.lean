import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_eq_monomial_iff {α : Type*} (a₁ a₂ : α →₀ ℕ) (b₁ b₂ : R) :
    MvPolynomial.monomial a₁ b₁ = MvPolynomial.monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := Finsupp.single_eq_single_iff _ _ _ _

