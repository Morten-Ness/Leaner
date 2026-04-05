import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_hom_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap := rfl

