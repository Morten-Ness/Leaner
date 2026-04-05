import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem smul_finsum {R M : Type*} [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (f : ι → M) : c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
  · exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

