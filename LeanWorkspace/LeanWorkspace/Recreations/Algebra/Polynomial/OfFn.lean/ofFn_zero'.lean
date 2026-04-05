import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_zero' (v : Fin 0 → R) : Polynomial.ofFn 0 v = 0 := rfl

