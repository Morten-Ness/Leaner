import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsRightRegular.pow_injective {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M}
    (hx : IsRightRegular x) (hx' : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) := MulOpposite.unop_injective.comp <| (isLeftRegular_op.mpr hx).pow_injective <|
    (MulOpposite.op_eq_one_iff x).not.mpr hx'

