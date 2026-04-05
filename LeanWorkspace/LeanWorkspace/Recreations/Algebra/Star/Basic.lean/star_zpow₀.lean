import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_zpow₀ [GroupWithZero R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z := op_injective <| (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

