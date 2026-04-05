import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_ceil_zero : (Nat.ceil : R → ℕ) ⁻¹' {0} = Iic 0 := ext fun _ => Nat.ceil_eq_zero

