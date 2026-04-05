import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
theorem surjective_toFn (n : ℕ) : Function.Surjective (Polynomial.toFn (R := R) n) :=
  open Classical in
  Function.RightInverse.surjective <| Polynomial.toFn_comp_ofFn_eq_id n

