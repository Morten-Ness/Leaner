import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_inv_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap := rfl

