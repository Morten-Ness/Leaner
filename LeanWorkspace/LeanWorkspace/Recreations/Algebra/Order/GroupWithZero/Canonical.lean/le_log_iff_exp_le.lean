import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem le_log_iff_exp_le (hx : x ≠ 0) : a ≤ log x ↔ exp a ≤ x := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

