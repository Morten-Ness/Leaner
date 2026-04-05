import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finsum_smul {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (f : ι → R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

