import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem inclusion_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) :
    Function.Injective (LieIdeal.inclusion h) := fun x y ↦ by
  simp only [LieIdeal.inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

