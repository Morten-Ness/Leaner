import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace (α χ : H → R)
    {x : L} (hx : x ∈ rootSpace H α) :
    MapsTo (toEnd R L M x) (genWeightSpace M χ) (genWeightSpace M (α + χ)) := by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (LieAlgebra.rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' ⊗ₜ m')).property

