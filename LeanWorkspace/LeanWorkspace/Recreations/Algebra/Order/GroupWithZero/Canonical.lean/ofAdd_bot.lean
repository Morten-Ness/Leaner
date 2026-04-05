import Mathlib

variable {α β : Type*}

theorem ofAdd_bot [LinearOrderedAddCommMonoidWithTop α] :
    Multiplicative.ofAdd ⊥ = (0 : Multiplicative αᵒᵈ) := rfl

