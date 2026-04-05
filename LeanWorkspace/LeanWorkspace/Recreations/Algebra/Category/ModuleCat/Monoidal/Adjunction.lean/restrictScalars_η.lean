import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem restrictScalars_η (r : R) :
    ε (restrictScalars f) r = f r := by
  letI := f.toAlgebra
  dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
  rw [extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.extendScalars_η]
  erw [AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra, mul_one]

