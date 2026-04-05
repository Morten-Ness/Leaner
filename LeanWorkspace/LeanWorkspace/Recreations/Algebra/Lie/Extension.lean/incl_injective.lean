import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem incl_injective (E : LieAlgebra.Extension R M L) :
    Function.Injective E.incl := (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot

