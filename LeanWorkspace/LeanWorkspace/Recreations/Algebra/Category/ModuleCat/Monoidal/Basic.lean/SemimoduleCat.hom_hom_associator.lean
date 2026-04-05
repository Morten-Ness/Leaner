import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_hom_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap := rfl

