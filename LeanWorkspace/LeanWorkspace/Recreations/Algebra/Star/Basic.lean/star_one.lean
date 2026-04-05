import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 := op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

