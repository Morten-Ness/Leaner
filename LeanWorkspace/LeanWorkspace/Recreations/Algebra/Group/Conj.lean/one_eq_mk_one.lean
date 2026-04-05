import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 := rfl

