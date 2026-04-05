import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_inv_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).inv.hom = (Algebra.TensorProduct.lid _ _).symm.toAlgHom := rfl

