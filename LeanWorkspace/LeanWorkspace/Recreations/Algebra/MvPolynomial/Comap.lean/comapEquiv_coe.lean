import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (MvPolynomial.comapEquiv f : (τ → R) → σ → R) = MvPolynomial.comap f := rfl

