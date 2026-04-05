import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem Polynomial.toMvPolynomial_injective (i : σ) :
    Function.Injective (toMvPolynomial (R := R) i) := by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x ↦ i) fun _ _ _ ↦ rfl

