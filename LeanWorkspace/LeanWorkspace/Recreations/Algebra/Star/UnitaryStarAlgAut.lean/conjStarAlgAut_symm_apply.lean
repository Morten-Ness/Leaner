import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (Unitary.conjStarAlgAut S R u).symm x = (star u : R) * x * u := rfl

