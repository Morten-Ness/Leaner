import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem invOf_pow (m : α) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟(m ^ n) = ⅟m ^ n := @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

