import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

theorem ofTwoCocycle_proj_apply (x : (LieAlgebra.Extension.ofTwoCocycle c).L) : (LieAlgebra.Extension.ofTwoCocycle c).proj x = x.carrier.1 := rfl

