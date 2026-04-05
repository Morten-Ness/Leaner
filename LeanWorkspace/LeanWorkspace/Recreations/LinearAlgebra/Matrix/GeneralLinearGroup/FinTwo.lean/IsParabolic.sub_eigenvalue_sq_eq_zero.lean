import Mathlib

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

theorem IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [Matrix.parabolicEigenvalue, -scalar_apply, Matrix.sub_scalar_sq_eq_discr, hm.2]

