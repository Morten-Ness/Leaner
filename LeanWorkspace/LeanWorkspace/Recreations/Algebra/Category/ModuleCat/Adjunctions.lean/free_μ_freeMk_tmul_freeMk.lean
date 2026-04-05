import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem free_μ_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    μ (ModuleCat.free R) _ _ (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) = ModuleCat.freeMk ⟨x, y⟩ := by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

