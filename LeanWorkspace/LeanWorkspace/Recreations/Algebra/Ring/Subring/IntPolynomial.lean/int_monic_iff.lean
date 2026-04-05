import Mathlib

open scoped Polynomial

variable {K : Type*} [Field K] (R : Subring K)

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

theorem int_monic_iff : (P.int R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← Polynomial.int_leadingCoeff_eq, OneMemClass.coe_eq_one]

