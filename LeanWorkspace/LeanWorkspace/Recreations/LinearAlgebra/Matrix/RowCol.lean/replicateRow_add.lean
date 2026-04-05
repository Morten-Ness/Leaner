import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_add [Add α] (v w : m → α) :
    Matrix.replicateRow ι (v + w) = Matrix.replicateRow ι v + Matrix.replicateRow ι w := by
  ext
  rfl

