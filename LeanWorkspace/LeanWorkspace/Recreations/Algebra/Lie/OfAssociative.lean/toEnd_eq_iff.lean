import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem toEnd_eq_iff [IsFaithful R L M] {x y : L} :
    toEnd R L M x = toEnd R L M y ↔ x = y := IsFaithful.injective_toEnd.eq_iff

