import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ := op_injective <| (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

