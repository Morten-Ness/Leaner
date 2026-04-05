import Mathlib

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : BilinForm R M)

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

theorem skewAdjointLieSubalgebraEquiv_apply
    (f : skewAdjointLieSubalgebra (B.compl₁₂ (Qₗ := N) (Qₗ' := N) ↑e ↑e)) :
    ↑(skewAdjointLieSubalgebraEquiv B e f) = e.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

