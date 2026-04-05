import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_sum {MvPolynomial.X : Type*} (s : Finset MvPolynomial.X) (f : MvPolynomial.X → MvPolynomial σ R) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, MvPolynomial.coeff m (f x) := map_sum (@MvPolynomial.coeffAddMonoidHom R σ _ _) _ s

