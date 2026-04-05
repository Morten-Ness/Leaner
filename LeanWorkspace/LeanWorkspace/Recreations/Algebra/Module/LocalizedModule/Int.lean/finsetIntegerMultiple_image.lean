import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') :
    f '' IsLocalizedModule.finsetIntegerMultiple S f s = IsLocalizedModule.commonDenomOfFinset S f s • (s : Set M') := by
  delta IsLocalizedModule.finsetIntegerMultiple IsLocalizedModule.commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [IsLocalizedModule.map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, IsLocalizedModule.map_integerMultiple S f s id _⟩

