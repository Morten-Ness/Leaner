import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_mul_replicateCol_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α)
    (i j) : (Matrix.replicateRow ι v * Matrix.replicateCol ι w) i j = v ⬝ᵥ w := rfl

