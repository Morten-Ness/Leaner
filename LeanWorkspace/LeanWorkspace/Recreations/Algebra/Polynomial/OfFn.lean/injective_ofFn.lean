import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem injective_ofFn (n : ℕ) : Function.Injective (Polynomial.ofFn (R := R) n) :=
  Function.LeftInverse.injective <| Polynomial.toFn_comp_ofFn_eq_id n

