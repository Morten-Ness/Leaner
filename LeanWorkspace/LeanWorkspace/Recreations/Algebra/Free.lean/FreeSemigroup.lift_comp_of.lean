import Mathlib

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_comp_of : FreeSemigroup.lift f ∘ FreeSemigroup.of = f := rfl

