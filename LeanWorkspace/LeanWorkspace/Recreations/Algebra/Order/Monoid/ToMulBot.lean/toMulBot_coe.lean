import Mathlib

variable {α : Type u}

variable [Add α]

theorem toMulBot_coe (x : Multiplicative α) :
    WithZero.toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) := rfl

