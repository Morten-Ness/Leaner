import Mathlib

variable {α : Type u}

theorem Units.val_mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a := rfl

