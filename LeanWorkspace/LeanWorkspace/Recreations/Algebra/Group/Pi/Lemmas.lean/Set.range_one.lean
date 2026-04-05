import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α → β) = {1} := range_const

