import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R]
    (s : S) (p : R[X]) (k : ℕ) : Polynomial.derivative^[k] (s • p) = s • Polynomial.derivative^[k] p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih]

