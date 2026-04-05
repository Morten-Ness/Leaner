import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem bind₁_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    MvPolynomial.bind₁ f (rename g φ) = MvPolynomial.bind₁ (f ∘ g) φ := AlgHom.congr_fun (MvPolynomial.bind₁_comp_rename f g) φ

