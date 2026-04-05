import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_star_apply (u : unitary R) (x : R) :
    Unitary.conjStarAlgAut S R (star u) x = (star u : R) * x * u := by simp

