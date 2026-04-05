import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : R → ℕ) ⁻¹' {n} = Ico (n : R) (n + 1) := ext fun _ => Nat.floor_eq_iff' hn

