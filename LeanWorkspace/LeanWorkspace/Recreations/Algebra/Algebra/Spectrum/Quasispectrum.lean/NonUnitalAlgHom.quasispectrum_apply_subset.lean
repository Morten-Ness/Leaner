import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem NonUnitalAlgHom.quasispectrum_apply_subset {F R A B : Type*}
    [CommRing R] [NonUnitalRing A] [NonUnitalRing B] [Module R A] [Module R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a := NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

