import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

theorem replicateCol_apply {ι : Type*} (w : m → α) (i) (j : ι) : Matrix.replicateCol ι w i j = w i := rfl

