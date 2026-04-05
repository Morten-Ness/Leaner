import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [ModuleCat.epi_iff_range_eq_top, LinearMap.range_eq_top]

