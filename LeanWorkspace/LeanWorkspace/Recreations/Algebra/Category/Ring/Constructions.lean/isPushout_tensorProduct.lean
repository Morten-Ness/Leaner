import Mathlib

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨CommRingCat.pushoutCoconeIsColimit R A B⟩

