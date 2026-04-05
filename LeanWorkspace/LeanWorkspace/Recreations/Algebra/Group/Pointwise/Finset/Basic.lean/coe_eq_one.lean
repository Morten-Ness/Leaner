import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

