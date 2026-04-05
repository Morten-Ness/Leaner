import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((MvPolynomial.comapEquiv f).symm : (σ → R) → τ → R) = MvPolynomial.comap f.symm := rfl

