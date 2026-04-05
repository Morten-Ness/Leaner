import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : Matrix.replicateRow ι (v ᵥ* M) = Matrix.replicateRow ι v * M := by
  ext
  rfl

