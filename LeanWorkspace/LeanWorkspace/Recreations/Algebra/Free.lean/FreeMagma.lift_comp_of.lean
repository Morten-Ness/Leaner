import Mathlib

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

theorem lift_comp_of : FreeMagma.lift f ∘ of = f := rfl

