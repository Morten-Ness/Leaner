import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem eval_zero_map (f : R →+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [← Polynomial.coeff_zero_eq_eval_zero]

