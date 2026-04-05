import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem lie_mem_maxGenEigenspace_toEnd
    {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y ∈ 𝕎(L, χ₁, x)) (hm : m ∈ 𝕎(M, χ₂, x)) :
    ⁅y, m⁆ ∈ 𝕎(M, χ₁ + χ₂, x) := by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]

