import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

theorem bracket (x y : (LieAlgebra.Extension.ofTwoCocycle c).L) :
    ⁅x, y⁆ = LieAlgebra.Extension.ofAlg c ⁅(LieAlgebra.Extension.ofAlg c).symm x, (LieAlgebra.Extension.ofAlg c).symm y⁆ := rfl

