import Mathlib

open scoped TensorProduct

variable (R A L : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

theorem twoCochainOfBilinear_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) (x y : loopAlgebra R A L) :
    LieAlgebra.LoopAlgebra.twoCochainOfBilinear R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm (LieAlgebra.LoopAlgebra.residuePairing R A L Φ x y) := rfl

