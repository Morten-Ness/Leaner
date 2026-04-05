import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_id_apply (p : MvPolynomial σ R) : MvPolynomial.rename id p = p := by
  simp

