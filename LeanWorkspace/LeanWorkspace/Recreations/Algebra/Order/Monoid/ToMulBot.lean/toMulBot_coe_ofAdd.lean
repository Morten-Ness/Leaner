import Mathlib

variable {α : Type u}

variable [Add α]

theorem toMulBot_coe_ofAdd (x : α) :
    WithZero.toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x := rfl

