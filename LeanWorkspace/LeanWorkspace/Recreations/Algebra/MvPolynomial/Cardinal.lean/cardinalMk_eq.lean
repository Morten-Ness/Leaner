import Mathlib

variable {σ R : Type u} [CommSemiring R]

theorem cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R := by simp

