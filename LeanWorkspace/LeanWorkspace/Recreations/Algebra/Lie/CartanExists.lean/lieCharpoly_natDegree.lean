import Mathlib

variable {K R L M : Type*}

variable [Field K] [CommRing R]

variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Module.Finite K L]

variable [Module.Finite R L] [Module.Free R L]

variable [Module.Finite R M] [Module.Free R M]

variable (x y : L)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem lieCharpoly_natDegree [Nontrivial R] : (LieAlgebra.engel_isBot_of_isMin.lieCharpoly R M x y).natDegree = finrank R M := by
  rw [LieAlgebra.engel_isBot_of_isMin.lieCharpoly, (polyCharpoly_monic _ _).natDegree_map, polyCharpoly_natDegree]

