import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.isUnit_iff_inverse_ne_zero [Nontrivial M₀] {x : M₀} : IsUnit x ↔ x⁻¹ʳ ≠ 0 := ⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt <| Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ

