import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x := Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

