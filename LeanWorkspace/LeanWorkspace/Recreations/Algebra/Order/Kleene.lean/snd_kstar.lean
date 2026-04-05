import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] [KleeneAlgebra β]

theorem snd_kstar (a : α × β) : a∗.2 = a.2∗ := rfl

