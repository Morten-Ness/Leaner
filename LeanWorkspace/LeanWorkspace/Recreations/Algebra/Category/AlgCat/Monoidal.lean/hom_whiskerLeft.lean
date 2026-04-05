import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_whiskerLeft (L : AlgCat.{u} R) {M N : AlgCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = Algebra.TensorProduct.map (.id _ _) f.hom := rfl

