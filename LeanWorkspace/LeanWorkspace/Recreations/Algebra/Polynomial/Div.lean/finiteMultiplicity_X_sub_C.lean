import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p ≠ 0) : FiniteMultiplicity (Polynomial.X - Polynomial.C a) p := by
  haveI := Nontrivial.of_polynomial_ne h0
  refine Polynomial.finiteMultiplicity_of_degree_pos_of_monic ?_ (Polynomial.monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

