import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivativeFinsupp_map [Semiring S] (p : R[X]) (f : R →+* S) :
    Polynomial.derivativeFinsupp (p.map f) = (Polynomial.derivativeFinsupp p).mapRange (·.map f) (by simp) := by
  ext i : 1
  simp

