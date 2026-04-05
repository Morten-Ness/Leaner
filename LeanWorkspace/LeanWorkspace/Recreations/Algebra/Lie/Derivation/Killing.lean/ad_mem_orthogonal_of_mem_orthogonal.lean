import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

theorem ad_mem_orthogonal_of_mem_orthogonal {D : LieDerivation R L L} (hD : D ∈ 𝕀ᗮ) (x : L) :
    ad R L (D x) ∈ 𝕀ᗮ := by
  simp only [ad_apply_lieDerivation, LieHom.range_toSubmodule, neg_mem_iff]
  exact (rangeAdOrthogonal R L).lie_mem hD

