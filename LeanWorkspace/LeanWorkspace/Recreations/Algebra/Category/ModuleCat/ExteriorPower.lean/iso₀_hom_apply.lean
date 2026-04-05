import Mathlib

variable {R : Type u} [CommRing R]

theorem iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 → M) :
    (ModuleCat.exteriorPower.iso₀ M).hom (ModuleCat.exteriorPower.mk f) = 1 := ModuleCat.exteriorPower.zeroEquiv_ιMulti _

