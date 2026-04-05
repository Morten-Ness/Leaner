import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_trans_conjStarAlgAut (u₁ u₂ : unitary R) :
    (Unitary.conjStarAlgAut S R u₁).trans (Unitary.conjStarAlgAut S R u₂) = Unitary.conjStarAlgAut S R (u₂ * u₁) := map_mul _ _ _ |>.symm

