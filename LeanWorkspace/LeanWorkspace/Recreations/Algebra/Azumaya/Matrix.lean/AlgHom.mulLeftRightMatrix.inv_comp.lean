import Mathlib

open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

theorem AlgHom.mulLeftRightMatrix.inv_comp :
    (AlgHom.mulLeftRightMatrix_inv R n).comp
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id := ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ ↦ by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]

