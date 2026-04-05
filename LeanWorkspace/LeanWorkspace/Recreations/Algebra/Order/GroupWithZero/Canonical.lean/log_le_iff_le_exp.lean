import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem log_le_iff_le_exp (hx : x ≠ 0) : log x ≤ a ↔ x ≤ exp a := by
  lift x to Multiplicative G using hx; simpa [log, exp] using .rfl

