import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

theorem ofTwoCocycle_incl_apply (x : M) : (LieAlgebra.Extension.ofTwoCocycle c).incl x = ⟨(0, x)⟩ := rfl

