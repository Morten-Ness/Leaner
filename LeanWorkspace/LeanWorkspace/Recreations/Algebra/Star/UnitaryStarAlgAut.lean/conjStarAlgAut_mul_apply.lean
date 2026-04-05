import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_mul_apply (u₁ u₂ : unitary R) (x : R) :
    Unitary.conjStarAlgAut S R (u₁ * u₂) x = Unitary.conjStarAlgAut S R u₁ (Unitary.conjStarAlgAut S R u₂ x) := by simp

