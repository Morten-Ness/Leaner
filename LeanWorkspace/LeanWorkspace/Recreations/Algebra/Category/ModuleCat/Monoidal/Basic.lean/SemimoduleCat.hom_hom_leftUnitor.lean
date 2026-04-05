import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_hom_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap := rfl

