import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_eq_one {α : Type*} [One α] {x : Additive α} :
    x.toMul = 1 ↔ x = 0 := Iff.rfl

