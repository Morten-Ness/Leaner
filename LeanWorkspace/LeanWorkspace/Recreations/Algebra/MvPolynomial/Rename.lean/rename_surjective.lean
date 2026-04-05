import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_surjective (f : σ → τ) (hf : Function.Surjective f) :
    Function.Surjective (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) := let ⟨_, hf⟩ := hf.hasRightInverse; MvPolynomial.rename_rightInverse hf |>.surjective

