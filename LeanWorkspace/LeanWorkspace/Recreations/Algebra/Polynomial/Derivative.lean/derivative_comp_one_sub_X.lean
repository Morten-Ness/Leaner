import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem derivative_comp_one_sub_X (p : R[X]) :
    Polynomial.derivative (p.comp (1 - Polynomial.X)) = -p.derivative.comp (1 - Polynomial.X) := by simp [Polynomial.derivative_comp]

