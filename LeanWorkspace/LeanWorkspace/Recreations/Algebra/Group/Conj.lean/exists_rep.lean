import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a := Quot.exists_rep a

