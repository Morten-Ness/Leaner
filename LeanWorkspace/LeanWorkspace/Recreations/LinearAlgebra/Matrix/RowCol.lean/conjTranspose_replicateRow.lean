import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem conjTranspose_replicateRow [Star α] (v : m → α) :
    (Matrix.replicateRow ι v)ᴴ = Matrix.replicateCol ι (star v) := by
  ext
  rfl

