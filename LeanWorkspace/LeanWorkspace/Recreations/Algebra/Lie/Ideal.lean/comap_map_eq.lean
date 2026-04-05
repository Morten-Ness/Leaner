import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem comap_map_eq (h : ↑(LieIdeal.map f I) = f '' I) : LieIdeal.comap f (LieIdeal.map f I) = I ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, LieIdeal.comap_toSubmodule, I.map_toSubmodule f h,
    LieSubmodule.sup_toSubmodule, LieHom.ker_toSubmodule f, Submodule.comap_map_eq]

