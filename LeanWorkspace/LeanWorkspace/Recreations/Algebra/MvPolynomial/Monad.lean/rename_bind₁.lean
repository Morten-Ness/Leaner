import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem rename_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (MvPolynomial.bind₁ f φ) = MvPolynomial.bind₁ (fun i => rename g <| f i) φ := AlgHom.congr_fun (MvPolynomial.rename_comp_bind₁ f g) φ

