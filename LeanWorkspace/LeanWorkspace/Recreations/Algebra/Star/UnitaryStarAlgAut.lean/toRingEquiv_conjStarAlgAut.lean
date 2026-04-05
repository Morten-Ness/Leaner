import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem toRingEquiv_conjStarAlgAut (u : unitary R) :
    (Unitary.conjStarAlgAut S R u).toRingEquiv =
      MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) := rfl

