import Mathlib

variable {R : Type u} [CommRing R]

theorem iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.exteriorPower.map f 1 ≫ (ModuleCat.exteriorPower.iso₁ N).hom = (ModuleCat.exteriorPower.iso₁ M).hom ≫ f := ModuleCat.hom_ext (ModuleCat.exteriorPower.oneEquiv_naturality f.hom)

