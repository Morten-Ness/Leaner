import Mathlib

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

theorem LieModuleEquiv.ofTop_apply (x : (⊤ : LieSubmodule R L M)) :
    LieModuleEquiv.ofTop R L M x = x := rfl

