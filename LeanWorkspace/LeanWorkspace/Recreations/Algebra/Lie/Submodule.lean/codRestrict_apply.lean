import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N]

variable (f : M →ₗ⁅R,L⁆ N)

theorem codRestrict_apply (P : LieSubmodule R L N) (f : M →ₗ⁅R,L⁆ N) (h : ∀ m, f m ∈ P) (m : M) :
    (f.codRestrict P h m : N) = f m := rfl

