import Mathlib

variable {R : Type u} [CommRing R]

theorem iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 → M) :
    (ModuleCat.exteriorPower.iso₁ M).hom (ModuleCat.exteriorPower.mk f) = f 0 := ModuleCat.exteriorPower.oneEquiv_ιMulti _

