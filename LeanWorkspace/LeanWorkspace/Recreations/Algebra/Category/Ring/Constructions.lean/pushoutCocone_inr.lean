import Mathlib

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem pushoutCocone_inr :
    (CommRingCat.pushoutCocone R A B).inr = ofHom (Algebra.TensorProduct.includeRight.toRingHom (A := B)) :=
  rfl

