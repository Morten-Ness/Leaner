import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem Polynomial.toMvPolynomial_eq_rename_comp (i : σ) :
    toMvPolynomial (R := R) i =
      (MvPolynomial.rename (fun _ : Unit ↦ i)).comp (MvPolynomial.pUnitAlgEquiv R).symm := by
  ext
  simp

