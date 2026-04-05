import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem transpose_replicateRow (v : m → α) : (Matrix.replicateRow ι v)ᵀ = Matrix.replicateCol ι v := by
  ext
  rfl

