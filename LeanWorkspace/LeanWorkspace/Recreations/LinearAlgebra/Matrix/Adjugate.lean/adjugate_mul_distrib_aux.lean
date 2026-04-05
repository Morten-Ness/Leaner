import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det)
    (hB : IsLeftRegular B.det) : Matrix.adjugate (A * B) = Matrix.adjugate B * Matrix.adjugate A := by
  have hAB : IsLeftRegular (A * B).det := by
    rw [Matrix.det_mul]
    exact hA.mul hB
  refine (Matrix.isRegular_of_isLeftRegular_det hAB).left ?_
  simp only
  rw [Matrix.mul_adjugate, Matrix.mul_assoc, ← Matrix.mul_assoc B, Matrix.mul_adjugate,
    smul_mul, Matrix.one_mul, mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, ← Matrix.det_mul]

