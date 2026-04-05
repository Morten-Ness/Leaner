import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.rename f φ) = constantCoeff φ := by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, MvPolynomial.rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, MvPolynomial.rename_X, constantCoeff_X, map_mul]

