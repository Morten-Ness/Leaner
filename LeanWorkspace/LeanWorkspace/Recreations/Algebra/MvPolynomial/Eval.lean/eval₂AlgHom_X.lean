import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

variable [Algebra R S₁] (g : σ → S₁)

theorem eval₂AlgHom_X (i : σ) :
    MvPolynomial.eval₂AlgHom R g (X i : MvPolynomial σ R) = g i := MvPolynomial.eval₂_X (algebraMap R S₁) g i

