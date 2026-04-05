import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem IsConj.refl (a : α) : IsConj a a := ⟨1, SemiconjBy.one_left a⟩

