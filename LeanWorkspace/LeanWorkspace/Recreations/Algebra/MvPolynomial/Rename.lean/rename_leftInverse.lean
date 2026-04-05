import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_leftInverse {f : σ → τ} {g : τ → σ} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) (MvPolynomial.rename g) := by
  intro x
  simp [hf.comp_eq_id]

