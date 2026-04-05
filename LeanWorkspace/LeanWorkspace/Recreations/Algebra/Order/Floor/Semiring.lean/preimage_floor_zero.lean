import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem preimage_floor_zero : (floor : R → ℕ) ⁻¹' {0} = Iio 1 := ext fun _ => Nat.floor_eq_zero

