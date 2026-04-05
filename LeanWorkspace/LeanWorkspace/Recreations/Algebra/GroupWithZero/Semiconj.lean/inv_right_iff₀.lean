import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := ⟨fun h => inv_inv x ▸ inv_inv y ▸ SemiconjBy.inv_right₀ h, SemiconjBy.inv_right₀⟩

