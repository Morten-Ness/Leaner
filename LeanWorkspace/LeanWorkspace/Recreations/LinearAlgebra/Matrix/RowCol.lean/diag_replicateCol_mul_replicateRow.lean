import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem diag_replicateCol_mul_replicateRow [Mul α] [AddCommMonoid α] [Unique ι] (a b : n → α) :
    diag (Matrix.replicateCol ι a * Matrix.replicateRow ι b) = a * b := by
  ext
  simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]

