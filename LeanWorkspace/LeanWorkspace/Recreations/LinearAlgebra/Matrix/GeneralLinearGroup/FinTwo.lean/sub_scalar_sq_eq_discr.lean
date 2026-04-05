import Mathlib

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

theorem sub_scalar_sq_eq_discr [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4) := by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

