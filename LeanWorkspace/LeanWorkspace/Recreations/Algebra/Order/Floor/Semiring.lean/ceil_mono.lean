import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem ceil_mono : Monotone (ceil : R → ℕ) := gc_ceil_coe.monotone_l

