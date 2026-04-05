import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (h : K ≤ K')

theorem equivOfLe_apply (x : K) : LieSubalgebra.equivOfLe h x = ⟨LieSubalgebra.inclusion h x, LieHom.mem_range_self (LieSubalgebra.inclusion h) x⟩ := rfl

