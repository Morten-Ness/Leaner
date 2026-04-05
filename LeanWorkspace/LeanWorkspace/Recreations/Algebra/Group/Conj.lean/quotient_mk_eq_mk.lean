import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a := rfl

