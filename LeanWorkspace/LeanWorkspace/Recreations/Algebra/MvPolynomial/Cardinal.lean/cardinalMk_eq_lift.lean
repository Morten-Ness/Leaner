import Mathlib

variable {σ : Type u} {R : Type v} [CommSemiring R]

theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = lift.{u} #R := by simp

