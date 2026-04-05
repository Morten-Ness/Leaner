import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem zeroRootSubalgebra_normalizer_eq_self :
    (LieAlgebra.zeroRootSubalgebra R L H).normalizer = LieAlgebra.zeroRootSubalgebra R L H := by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [LieAlgebra.mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (LieAlgebra.le_zeroRootSubalgebra R L H hy)
  rw [LieAlgebra.mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew, map_neg, neg_eq_zero] at hk
  use k + 1
  rw [Module.End.iterate_succ, LinearMap.coe_comp, Function.comp_apply, toEnd_apply_apply,
    LieSubalgebra.coe_bracket_of_module, Submodule.coe_mk, hk]

