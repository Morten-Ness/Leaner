import Mathlib

variable {ι α β : Type*}

theorem ceilDiv_eq_add_pred_div (a b : ℕ) : a ⌈/⌉ b = (a + b - 1) / b := rfl

