import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [LieHom.isIdealMorphism_def, LieHom.idealRange_eq_top_of_surjective f h, LieHom.range_eq_top f.mpr h,
    LieIdeal.top_toLieSubalgebra]

