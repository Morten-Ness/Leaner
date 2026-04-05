import Mathlib

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : BilinForm R M)

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

theorem skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) :
    ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

