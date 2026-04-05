import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R]

theorem nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) :
    Polynomial.nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [Polynomial.nextCoeffUp, if_neg (Polynomial.natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

