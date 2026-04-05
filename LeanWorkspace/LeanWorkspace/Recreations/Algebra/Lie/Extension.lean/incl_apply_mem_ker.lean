import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem incl_apply_mem_ker (E : LieAlgebra.Extension R M L) (x : M) :
    E.incl x ∈ E.proj.ker := Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x

