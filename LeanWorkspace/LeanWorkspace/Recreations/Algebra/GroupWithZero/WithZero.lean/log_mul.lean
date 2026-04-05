import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddMonoid M]

theorem log_mul {x y : Mᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : WithZero.log (x * y) = WithZero.log x + WithZero.log y := by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl

