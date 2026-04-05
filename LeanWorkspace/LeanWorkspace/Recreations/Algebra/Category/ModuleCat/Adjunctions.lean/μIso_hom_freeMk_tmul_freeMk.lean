import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (ModuleCat.FreeMonoidal.μIso R X Y).hom (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) = ModuleCat.freeMk ⟨x, y⟩ := by
  dsimp [ModuleCat.FreeMonoidal.μIso, ModuleCat.freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

