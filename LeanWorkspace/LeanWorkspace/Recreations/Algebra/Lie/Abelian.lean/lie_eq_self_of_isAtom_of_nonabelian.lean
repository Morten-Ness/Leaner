import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

theorem lie_eq_self_of_isAtom_of_nonabelian {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) (hI : IsAtom I) (h : ¬IsLieAbelian I) :
    ⁅I, I⁆ = I := lie_eq_self_of_isAtom_of_ne_bot hI <| not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

