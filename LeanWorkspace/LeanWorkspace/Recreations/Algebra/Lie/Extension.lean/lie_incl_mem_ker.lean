import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem lie_incl_mem_ker {E : LieAlgebra.Extension R M L} (x : E.L) (y : M) :
    ⁅x, E.incl y⁆ ∈ E.proj.ker := by
  rw [LieHom.mem_ker, LieHom.map_lie, proj_incl, lie_zero]

