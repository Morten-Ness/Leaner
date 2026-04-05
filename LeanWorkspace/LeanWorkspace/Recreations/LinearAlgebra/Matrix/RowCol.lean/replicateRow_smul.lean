import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_smul [SMul R α] (x : R) (v : m → α) :
    Matrix.replicateRow ι (x • v) = x • Matrix.replicateRow ι v := by
  ext
  rfl

