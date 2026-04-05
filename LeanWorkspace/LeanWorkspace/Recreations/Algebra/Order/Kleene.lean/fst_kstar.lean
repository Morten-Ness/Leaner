import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] [KleeneAlgebra β]

theorem fst_kstar (a : α × β) : a∗.1 = a.1∗ := rfl

