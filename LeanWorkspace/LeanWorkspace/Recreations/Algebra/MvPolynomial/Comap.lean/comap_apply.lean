import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    MvPolynomial.comap f x i = aeval x (f (X i)) := rfl

