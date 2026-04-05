import Mathlib

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [DecidableEq n] [Fintype n]

variable (J : Matrix n n R)

theorem skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invertible P)
    (A : skewAdjointMatricesLieSubalgebra J) :
    ↑(skewAdjointMatricesLieSubalgebraEquiv J P h A) = P⁻¹ * A * P := by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

