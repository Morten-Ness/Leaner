import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_hom_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).hom.hom = (Algebra.TensorProduct.assoc R R R M N K).toAlgHom := rfl

