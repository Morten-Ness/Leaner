import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_C_mul (a : R) (p : R[X]) (k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.C a * p) = Polynomial.C a * Polynomial.derivative^[k] p := by
  simp_rw [← smul_eq_C_mul, Polynomial.iterate_derivative_smul]

