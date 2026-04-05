import Mathlib

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_comp_of' (f : FreeSemigroup α →ₙ* β) : FreeSemigroup.lift (f ∘ FreeSemigroup.of) = f := FreeSemigroup.hom_ext rfl

