import Mathlib

variable {R A : Type*}

theorem charZero_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) [CharZero R] : CharZero A where
  cast_injective _ _ _ := CharZero.cast_injective <| h <| by simpa only [map_natCast f]

