import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ R} {b : (σ →₀ ℕ) → R → A} :
    p.sum b = ∑ m ∈ p.support, b m (p.coeff m) := by simp [MvPolynomial.support, Finsupp.sum, MvPolynomial.coeff]

