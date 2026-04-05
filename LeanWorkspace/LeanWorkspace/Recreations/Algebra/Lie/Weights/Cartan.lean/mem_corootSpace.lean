import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

set_option backward.isDefEq.respectTransparency false in
theorem mem_corootSpace {x : H} :
    x ∈ LieAlgebra.corootSpace α ↔
    (x : L) ∈ Submodule.span R {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} := by
  have : x ∈ LieAlgebra.corootSpace α ↔
      (x : L) ∈ LieSubmodule.map H.toLieSubmodule.incl (LieAlgebra.corootSpace α) := by
    rw [LieAlgebra.corootSpace]
    simp only [LieAlgebra.rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw [this, LieAlgebra.corootSpace, ← LieModuleHom.map_top, ← LieSubmodule.mem_toSubmodule,
    LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule, ← TensorProduct.span_tmul_eq_top,
    LinearMap.map_span, Set.image, Set.mem_setOf_eq, exists_exists_exists_and_eq]
  change (x : L) ∈ Submodule.span R
    {x | ∃ (a : rootSpace H α) (b : rootSpace H (-α)), ⁅(a : L), (b : L)⁆ = x} ↔ _
  simp

