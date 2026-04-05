import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem toFn_comp_ofFn_eq_id (n : ℕ) (v : Fin n → R) : Polynomial.toFn n (Polynomial.ofFn n v) = v := by
  simp [Polynomial.toFn, Polynomial.ofFn, LinearMap.pi]

