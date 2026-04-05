import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem det_add_replicateCol_mul_replicateRow {ι : Type*} [Unique ι]
    {A : Matrix m m α} (hA : IsUnit A.det) (u v : m → α) :
    (A + replicateCol ι u * replicateRow ι v).det =
    A.det * (1 + replicateRow ι v * A⁻¹ * replicateCol ι u).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (replicateCol ι u * replicateRow ι v),
    ← Matrix.mul_add, det_mul, ← Matrix.mul_assoc, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc]

