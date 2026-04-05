import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem transpose_replicateCol (v : m → α) : (Matrix.replicateCol ι v)ᵀ = Matrix.replicateRow ι v := by
  ext
  rfl

