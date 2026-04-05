import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_inv_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap := rfl

