import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_nsmul [Monoid α] (n : ℕ) (a : Additive α) : (n • a).toMul = a.toMul ^ n := rfl

