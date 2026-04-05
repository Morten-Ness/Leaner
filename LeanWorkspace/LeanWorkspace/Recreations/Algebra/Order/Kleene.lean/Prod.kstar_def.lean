import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] [KleeneAlgebra β]

theorem kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) := rfl

