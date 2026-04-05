import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 := ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

