import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

set_option backward.isDefEq.respectTransparency false in
theorem det_one_add_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] (u v : m → α) :
    det (1 + replicateCol ι u * replicateRow ι v) = 1 + v ⬝ᵥ u := by
  rw [Matrix.det_one_add_mul_comm, det_unique, Pi.add_apply, Pi.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply]

