import Mathlib

variable {α β : Type*}

theorem ofDual_toAdd_eq_top_iff [LinearOrderedAddCommMonoidWithTop α]
    (x : Multiplicative αᵒᵈ) : OrderDual.ofDual x.toAdd = ⊤ ↔ x = 0 := Iff.rfl

