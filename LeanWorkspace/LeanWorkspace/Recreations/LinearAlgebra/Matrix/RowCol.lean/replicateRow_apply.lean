import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem replicateRow_apply (v : n → α) (i : ι) (j) : Matrix.replicateRow ι v i j = v j := rfl

