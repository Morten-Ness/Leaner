import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_hom_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap := rfl

