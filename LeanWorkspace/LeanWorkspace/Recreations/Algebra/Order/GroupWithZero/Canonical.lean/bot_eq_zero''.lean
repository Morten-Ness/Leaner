import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

theorem bot_eq_zero'' : (⊥ : α) = 0 := eq_of_forall_ge_iff fun _ ↦ by simp

-- See note [lower instance priority]

