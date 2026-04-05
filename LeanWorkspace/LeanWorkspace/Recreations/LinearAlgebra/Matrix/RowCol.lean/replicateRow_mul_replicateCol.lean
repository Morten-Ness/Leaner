import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_mul_replicateCol [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) :
    Matrix.replicateRow ι v * Matrix.replicateCol ι w = of fun _ _ => v ⬝ᵥ w := rfl

