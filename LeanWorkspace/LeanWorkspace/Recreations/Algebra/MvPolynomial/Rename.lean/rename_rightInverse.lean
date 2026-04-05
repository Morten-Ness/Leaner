import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_rightInverse {f : σ → τ} {g : τ → σ} (hf : Function.RightInverse f g) :
    Function.RightInverse (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) (MvPolynomial.rename g) := MvPolynomial.rename_leftInverse hf

