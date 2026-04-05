import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

theorem corootSpace_zero_eq_bot :
    corootSpace (0 : H → K) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  suffices {x | ∃ y ∈ H, ∃ z ∈ H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z, hz⟩ : H)⁆ = 0 by
    simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using this
  simp

