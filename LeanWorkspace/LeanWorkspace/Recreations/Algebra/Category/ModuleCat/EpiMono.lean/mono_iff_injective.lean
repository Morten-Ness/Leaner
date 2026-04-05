import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [ModuleCat.mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

