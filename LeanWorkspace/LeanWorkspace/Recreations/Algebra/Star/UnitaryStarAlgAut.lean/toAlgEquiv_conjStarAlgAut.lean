import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R) :
    (Unitary.conjStarAlgAut S R u).toAlgEquiv =
      MulSemiringAction.toAlgEquiv _ R (ConjAct.toConjAct <| toUnits u) := rfl

