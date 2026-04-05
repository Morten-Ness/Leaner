import Mathlib

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem pushoutCocone_inl :
    (CommRingCat.pushoutCocone R A B).inl = ofHom (Algebra.TensorProduct.includeLeftRingHom (A := A)) :=
  rfl

