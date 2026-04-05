import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (h : N ≤ N')

theorem inclusion_injective : Function.Injective (LieSubmodule.inclusion h) := fun x y ↦ by
  simp only [LieSubmodule.inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

