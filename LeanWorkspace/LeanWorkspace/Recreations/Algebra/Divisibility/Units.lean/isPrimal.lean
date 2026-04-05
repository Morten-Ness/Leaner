import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem isPrimal (hu : IsUnit u) : IsPrimal u := fun _ _ _ ↦ ⟨u, 1, IsUnit.dvd hu, one_dvd _, (mul_one u).symm⟩

