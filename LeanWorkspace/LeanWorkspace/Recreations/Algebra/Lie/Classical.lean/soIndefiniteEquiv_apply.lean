import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

set_option backward.isDefEq.respectTransparency false in
theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : LieAlgebra.Orthogonal.so' p q R) :
    (LieAlgebra.Orthogonal.soIndefiniteEquiv p q R hi A : Matrix (p ⊕ q) (p ⊕ q) R) =
      (LieAlgebra.Orthogonal.Pso p q R i)⁻¹ * (A : Matrix (p ⊕ q) (p ⊕ q) R) * LieAlgebra.Orthogonal.Pso p q R i := by
  rw [LieAlgebra.Orthogonal.soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  grind [skewAdjointMatricesLieSubalgebraEquiv_apply]

