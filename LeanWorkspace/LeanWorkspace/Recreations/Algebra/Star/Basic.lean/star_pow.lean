import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_pow [Monoid R] [StarMul R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n := op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

