import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

theorem comap_mono : Monotone (LieIdeal.comap f) := fun J₁ J₂ h ↦ by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h

