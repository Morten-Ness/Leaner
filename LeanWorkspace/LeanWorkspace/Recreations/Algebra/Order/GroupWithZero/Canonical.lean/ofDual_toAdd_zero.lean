import Mathlib

variable {α β : Type*}

theorem ofDual_toAdd_zero [LinearOrderedAddCommMonoidWithTop α] :
    OrderDual.ofDual (0 : Multiplicative αᵒᵈ).toAdd = ⊤ := rfl

