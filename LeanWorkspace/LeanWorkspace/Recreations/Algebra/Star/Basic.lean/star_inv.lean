import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ := op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

