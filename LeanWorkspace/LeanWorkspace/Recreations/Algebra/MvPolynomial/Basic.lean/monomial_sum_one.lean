import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_sum_one {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) :
    (MvPolynomial.monomial (∑ i ∈ s, f i) 1 : MvPolynomial σ R) = ∏ i ∈ s, MvPolynomial.monomial (f i) 1 := map_prod (MvPolynomial.monomialOneHom R σ) (fun i => Multiplicative.ofAdd (f i)) s

