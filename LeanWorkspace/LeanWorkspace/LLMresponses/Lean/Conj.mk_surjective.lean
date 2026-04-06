import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) := by
  rintro ⟨a⟩
  exact ⟨a, rfl⟩
