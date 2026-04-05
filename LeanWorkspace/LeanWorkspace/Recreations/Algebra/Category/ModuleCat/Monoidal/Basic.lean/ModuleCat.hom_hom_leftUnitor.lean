import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_hom_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap := rfl

