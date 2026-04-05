import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

variable [Module.Finite R L]

theorem ad_mem_ker_killingForm_ad_range_of_mem_orthogonal
    {D : LieDerivation R L L} (hD : D ∈ 𝕀ᗮ) (x : L) :
    ad R L (D x) ∈ (LinearMap.ker (killingForm R 𝕀)).map (LieHom.range (ad R L)).subtype := by
  rw [← LieDerivation.IsKilling.killingForm_restrict_range_ad]
  exact LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl ⟨by simp, LieDerivation.IsKilling.ad_mem_orthogonal_of_mem_orthogonal hD x⟩

