import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (ModuleCat.FreeMonoidal.μIso R X Y).hom (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) = ModuleCat.freeMk ⟨x, y⟩ := by
  change finsuppTensorFinsupp' R X Y (ModuleCat.freeMk x ⊗ₜ[R] ModuleCat.freeMk y) = ModuleCat.freeMk ⟨x, y⟩
  simp [ModuleCat.freeMk, finsuppTensorFinsupp']
