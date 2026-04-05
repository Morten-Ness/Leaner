import Mathlib

variable {α : Type u} {β : Type v} (f : α → β)

theorem map_of (x) : FreeMagma.map f (of x) = of (f x) := rfl

