import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem self_mem_engel (x : L) : x ∈ LieSubalgebra.engel R x := by
  simp only [LieSubalgebra.mem_engel_iff]
  exact ⟨1, by simp⟩

