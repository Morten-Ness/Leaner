import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateCol_add [Add α] (v w : m → α) :
    Matrix.replicateCol ι (v + w) = Matrix.replicateCol ι v + Matrix.replicateCol ι w := by
  ext
  rfl

