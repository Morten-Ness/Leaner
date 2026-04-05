import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_hom_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).hom.hom = (Algebra.TensorProduct.rid _ _ _).toAlgHom := rfl

