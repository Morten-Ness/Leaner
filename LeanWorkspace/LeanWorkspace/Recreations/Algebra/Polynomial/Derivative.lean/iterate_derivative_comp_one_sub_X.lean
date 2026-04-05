import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem iterate_derivative_comp_one_sub_X (p : R[X]) (k : ℕ) :
    Polynomial.derivative^[k] (p.comp (1 - Polynomial.X)) = (-1) ^ k * (Polynomial.derivative^[k] p).comp (1 - Polynomial.X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (Polynomial.derivative p), Polynomial.derivative_comp, pow_succ]

