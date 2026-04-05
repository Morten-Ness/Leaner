import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (h : K ≤ K')

theorem inclusion_injective : Function.Injective (LieSubalgebra.inclusion h) := fun x y ↦ by
  simp only [LieSubalgebra.inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

