import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_whiskerRight {L M : AlgCat.{u} R} (f : L ⟶ M) (N : AlgCat.{u} R) :
    (f ▷ N).hom = Algebra.TensorProduct.map f.hom (.id _ _) := rfl

