import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_inv_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap := rfl

