import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a := rfl

