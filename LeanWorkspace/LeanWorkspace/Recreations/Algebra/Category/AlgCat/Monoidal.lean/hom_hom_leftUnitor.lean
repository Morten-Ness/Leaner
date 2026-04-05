import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_hom_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).hom.hom = (Algebra.TensorProduct.lid _ _).toAlgHom := rfl

