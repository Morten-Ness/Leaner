import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem conjTranspose_replicateCol [Star α] (v : m → α) :
    (Matrix.replicateCol ι v)ᴴ = Matrix.replicateRow ι (star v) := by
  ext
  rfl

