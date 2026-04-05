import Mathlib

variable {α : Type u}

variable [Add α]

theorem toMulBot_zero : WithZero.toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ := rfl

