import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (h : K ≤ K')

theorem ofLe_eq_comap_incl : LieSubalgebra.ofLe h = K.comap K'.incl := by
  ext
  rw [LieSubalgebra.mem_ofLe]
  rfl

