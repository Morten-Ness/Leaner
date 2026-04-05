import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

theorem lie_eq_self_of_isAtom_of_ne_bot (hN : IsAtom N) (h : ⁅I, N⁆ ≠ ⊥) : ⁅I, N⁆ = N := (hN.le_iff_eq h).mp <| LieSubmodule.lie_le_right N I

-- TODO: introduce typeclass for perfect Lie algebras and use it here in the conclusion

