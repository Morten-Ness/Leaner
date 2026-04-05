import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_inv_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap := rfl

