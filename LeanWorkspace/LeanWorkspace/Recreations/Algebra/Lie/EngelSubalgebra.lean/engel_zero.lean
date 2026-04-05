import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem engel_zero : LieSubalgebra.engel R (0 : L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [LieSubalgebra.mem_engel_iff, map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

