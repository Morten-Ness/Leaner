import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x := SemiconjBy.inv_symm_left_iff₀.2 h

