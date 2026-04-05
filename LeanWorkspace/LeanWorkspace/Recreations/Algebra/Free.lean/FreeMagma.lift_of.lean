import Mathlib

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

theorem lift_of (x) : FreeMagma.lift f (of x) = f x := rfl

