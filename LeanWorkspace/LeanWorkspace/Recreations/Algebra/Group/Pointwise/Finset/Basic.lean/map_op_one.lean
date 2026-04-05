import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem map_op_one : (1 : Finset α).map opEquiv.toEmbedding = 1 := rfl

