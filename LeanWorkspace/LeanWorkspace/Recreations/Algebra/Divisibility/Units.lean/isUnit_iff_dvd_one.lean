import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 := ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

