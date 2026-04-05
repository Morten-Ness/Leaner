import Mathlib

variable {α β : Type*}

theorem ofAdd_toDual_eq_zero_iff [LinearOrderedAddCommMonoidWithTop α]
    (x : α) : Multiplicative.ofAdd (OrderDual.toDual x) = 0 ↔ x = ⊤ := Iff.rfl

