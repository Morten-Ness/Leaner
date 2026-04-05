import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem proj_surjective (E : LieAlgebra.Extension R M L) :
    Function.Surjective E.proj := (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

