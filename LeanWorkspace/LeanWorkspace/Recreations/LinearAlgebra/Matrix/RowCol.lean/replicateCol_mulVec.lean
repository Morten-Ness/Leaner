import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateCol_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n → α) : Matrix.replicateCol ι (M *ᵥ v) = M * Matrix.replicateCol ι v := by
  ext
  rfl

