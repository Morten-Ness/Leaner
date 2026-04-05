import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_inv_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap := rfl

