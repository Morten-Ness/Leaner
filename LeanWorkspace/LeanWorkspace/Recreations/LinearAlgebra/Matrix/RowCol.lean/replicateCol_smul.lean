import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateCol_smul [SMul R α] (x : R) (v : m → α) :
    Matrix.replicateCol ι (x • v) = x • Matrix.replicateCol ι v := by
  ext
  rfl

