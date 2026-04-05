import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_finsupp_sum_index {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → σ →₀ ℕ)
    (a : R) : MvPolynomial.monomial (f.sum g) a = MvPolynomial.C a * f.prod fun a b => MvPolynomial.monomial (g a b) 1 := MvPolynomial.monomial_sum_index _ _ _

