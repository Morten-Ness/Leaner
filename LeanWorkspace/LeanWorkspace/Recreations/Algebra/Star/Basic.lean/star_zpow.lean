import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_zpow [Group R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z := op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

