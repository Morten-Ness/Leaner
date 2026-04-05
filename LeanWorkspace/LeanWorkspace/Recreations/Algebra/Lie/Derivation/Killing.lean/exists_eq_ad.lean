import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

variable [Module.Finite R L]

variable [LieAlgebra.IsKilling R L]

theorem exists_eq_ad (D : 𝔻) : ∃ x, ad R L x = D := by
  change D ∈ 𝕀
  rw [LieDerivation.IsKilling.range_ad_eq_top R L]
  exact Submodule.mem_top

