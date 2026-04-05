import Mathlib

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
    coeff (det ((Polynomial.X : α[Polynomial.X]) • A.map Polynomial.C + B.map Polynomial.C)) (Fintype.card n) = det A := by
  rw [Matrix.det_apply, Matrix.det_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Finset.mem_univ, forall_true_left]
  intro g
  convert coeff_smul (R := α) (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  · simp [coeff_C]
  · rintro p -
    dsimp only [add_apply, smul_apply, Matrix.map_apply, smul_eq_mul]
    compute_degree

