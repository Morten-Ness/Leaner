import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← LieHom.range_eq_top f] at h
  rw [LieHom.idealRange_eq_lieSpan_range, h, ← LieSubalgebra.coe_toSubmodule, ←
    LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule,
    LieSubalgebra.top_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodule.top_toSubmodule

