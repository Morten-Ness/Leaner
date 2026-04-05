import Mathlib

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

theorem coeff_det_X_add_C_zero (A B : Matrix n n α) :
    coeff (det ((Polynomial.X : α[Polynomial.X]) • A.map Polynomial.C + B.map Polynomial.C)) 0 = det B := by
  rw [Matrix.det_apply, finset_sum_coeff, Matrix.det_apply]
  refine Finset.sum_congr rfl ?_
  rintro g -
  convert coeff_smul (R := α) (sign g) _ 0
  rw [coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  simp

