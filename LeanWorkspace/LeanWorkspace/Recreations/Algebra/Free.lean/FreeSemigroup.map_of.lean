import Mathlib

variable {α : Type u}

variable {β : Type v} (f : α → β)

theorem map_of (x) : FreeSemigroup.map f (FreeSemigroup.of x) = FreeSemigroup.of (f x) := rfl

