import Mathlib

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem pushoutCocone_pt :
    (CommRingCat.pushoutCocone R A B).pt = CommRingCat.of (A ⊗[R] B) := rfl

