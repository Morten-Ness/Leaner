import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem algHom_C {A : Type*} [Semiring A] [Algebra R A] (f : MvPolynomial σ R →ₐ[R] A) (r : R) :
    f (MvPolynomial.C r) = algebraMap R A r := f.commutes r

