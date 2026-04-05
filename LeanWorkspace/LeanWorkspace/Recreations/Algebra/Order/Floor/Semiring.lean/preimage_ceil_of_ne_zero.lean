import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : R → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : R) n := ext fun _ => Nat.ceil_eq_iff hn

