import Mathlib

variable {R : Type*} [Ring R]

theorem injective_upperRightHom : Function.Injective (Matrix.GeneralLinearGroup.upperRightHom (R := R)) := by
  refine (injective_iff_map_eq_zero (Matrix.GeneralLinearGroup.upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

