import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_inv_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).inv.hom = (Algebra.TensorProduct.rid _ _ _).symm.toAlgHom := rfl

