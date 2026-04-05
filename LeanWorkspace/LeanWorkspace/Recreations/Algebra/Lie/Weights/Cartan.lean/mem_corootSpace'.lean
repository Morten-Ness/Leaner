import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

theorem mem_corootSpace' {x : H} :
    x ∈ LieAlgebra.corootSpace α ↔
    x ∈ Submodule.span R ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H) := by
  set s : Set H := ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [SetLike.mem_coe]
    rw [← Submodule.mem_map, Submodule.coe_subtype, Submodule.map_span, LieAlgebra.mem_corootSpace, ← this]
  ext u
  simp only [Submodule.coe_subtype, mem_image, Subtype.exists, LieSubalgebra.mem_toSubmodule,
    exists_and_right, exists_eq_right, mem_setOf_eq, s]
  refine ⟨fun ⟨_, y, hy, z, hz, hyz⟩ ↦ ⟨y, hy, z, hz, hyz⟩,
    fun ⟨y, hy, z, hz, hyz⟩ ↦ ⟨?_, y, hy, z, hz, hyz⟩⟩
  convert
    (LieAlgebra.rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) (⟨y, hy⟩ ⊗ₜ[R] ⟨z, hz⟩)).property using 0
  simp [hyz]

