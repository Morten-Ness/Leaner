import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_zsmul [DivInvMonoid α] (z : ℤ) (a : Additive α) : (z • a).toMul = a.toMul ^ z := rfl

