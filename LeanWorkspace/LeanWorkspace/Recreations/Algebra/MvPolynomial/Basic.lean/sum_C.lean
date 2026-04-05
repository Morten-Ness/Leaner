import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem sum_C {A : Type*} [AddCommMonoid A] {b : (σ →₀ ℕ) → R → A} (w : b 0 0 = 0) :
    sum (MvPolynomial.C a) b = b 0 a := MvPolynomial.sum_monomial_eq w

