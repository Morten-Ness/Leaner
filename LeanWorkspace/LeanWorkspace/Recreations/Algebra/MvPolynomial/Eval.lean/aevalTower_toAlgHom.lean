import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]

variable [Algebra S R] [Algebra S A] [Algebra S B]

variable (g : R →ₐ[S] A) (y : σ → A)

theorem aevalTower_toAlgHom (x : R) :
    MvPolynomial.aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x := MvPolynomial.aevalTower_algebraMap _ _ _

