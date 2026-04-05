import Mathlib

section

open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where
  eq_of_smul_eq_smul := by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

end
