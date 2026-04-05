import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem mem_idealRange_iff (h : LieHom.IsIdealMorphism f) {y : L'} :
    y ∈ LieHom.idealRange f ↔ ∃ x : L, f x = y := by
  rw [LieHom.isIdealMorphism_def f] at h
  rw [← LieSubmodule.mem_coe, ← LieIdeal.coe_toLieSubalgebra, h, f.coe_range, Set.mem_range]

