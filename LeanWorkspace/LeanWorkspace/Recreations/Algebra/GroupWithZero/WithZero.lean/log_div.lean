import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddGroup G]

theorem log_div {x y : Gᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : WithZero.log (x / y) = WithZero.log x - WithZero.log y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl

