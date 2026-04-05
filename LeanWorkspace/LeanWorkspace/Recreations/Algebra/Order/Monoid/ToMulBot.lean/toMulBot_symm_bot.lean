import Mathlib

variable {α : Type u}

variable [Add α]

theorem toMulBot_symm_bot : WithZero.toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 := rfl

