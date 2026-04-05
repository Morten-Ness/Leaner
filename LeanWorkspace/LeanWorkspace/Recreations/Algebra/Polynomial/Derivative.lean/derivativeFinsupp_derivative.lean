import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivativeFinsupp_derivative (p : R[X]) :
    Polynomial.derivativeFinsupp (Polynomial.derivative p) =
      (Polynomial.derivativeFinsupp p).comapDomain Nat.succ Nat.succ_injective.injOn := by
  ext i : 1
  simp

