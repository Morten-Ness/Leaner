import Mathlib

variable (R : Type u)

variable [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem μIso_inv_freeMk {X Y : Type u} (z : X ⊗ Y) :
    (ModuleCat.FreeMonoidal.μIso R X Y).inv (ModuleCat.freeMk z) = ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 := by
  dsimp [ModuleCat.FreeMonoidal.μIso, ModuleCat.freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

