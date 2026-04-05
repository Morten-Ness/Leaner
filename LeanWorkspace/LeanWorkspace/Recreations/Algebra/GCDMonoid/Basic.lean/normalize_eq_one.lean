import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x := ⟨fun hx => isUnit_iff_exists_inv.2 ⟨_, hx⟩, fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u⟩

