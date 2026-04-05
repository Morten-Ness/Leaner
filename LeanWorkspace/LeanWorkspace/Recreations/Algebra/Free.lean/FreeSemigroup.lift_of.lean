import Mathlib

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_of (x : α) : FreeSemigroup.lift f (FreeSemigroup.of x) = f x := rfl

