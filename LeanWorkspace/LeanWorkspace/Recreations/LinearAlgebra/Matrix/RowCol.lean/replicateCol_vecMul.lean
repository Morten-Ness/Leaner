import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateCol_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : Matrix.replicateCol ι (v ᵥ* M) = (Matrix.replicateRow ι v * M)ᵀ := by
  ext
  rfl

