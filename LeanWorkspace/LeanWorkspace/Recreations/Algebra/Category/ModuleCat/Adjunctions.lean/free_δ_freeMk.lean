import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem free_δ_freeMk {X Y : Type u} (z : X ⊗ Y) :
    δ (ModuleCat.free R) _ _ (ModuleCat.freeMk z) = ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 := by
  apply FreeMonoidal.μIso_inv_freeMk

