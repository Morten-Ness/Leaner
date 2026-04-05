import Mathlib

section

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

end

section

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem isPrimal (hu : IsUnit u) : IsPrimal u := fun _ _ _ ↦ ⟨u, 1, IsUnit.dvd hu, one_dvd _, (mul_one u).symm⟩

end
