import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_hom_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap := rfl

