import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem cast_mul_floor_div_cancel {R : Type*} [CommSemiring R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {n : ℕ} (hn : n ≠ 0) (a : R) :
    ⌊n * a⌋₊ / n = ⌊a⌋₊ := by
  rw [mul_comm, Nat.mul_cast_floor_div_cancel hn]

