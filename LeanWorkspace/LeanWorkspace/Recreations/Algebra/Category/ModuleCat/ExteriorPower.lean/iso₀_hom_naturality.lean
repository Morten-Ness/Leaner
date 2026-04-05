import Mathlib

variable {R : Type u} [CommRing R]

theorem iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.exteriorPower.map f 0 ≫ (ModuleCat.exteriorPower.iso₀ N).hom = (ModuleCat.exteriorPower.iso₀ M).hom := ModuleCat.hom_ext (ModuleCat.exteriorPower.zeroEquiv_naturality f.hom)

