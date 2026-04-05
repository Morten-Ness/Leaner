import Mathlib

variable {α : Type*}

variable [MonoidWithZero α]

theorem isPrimal_zero : IsPrimal (0 : α) := fun a b h ↦ ⟨a, b, dvd_rfl, dvd_rfl, (zero_dvd_iff.mp h).symm⟩

