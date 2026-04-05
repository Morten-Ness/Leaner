import Mathlib

variable (A B : CommRingCat.{u})

theorem coproductCocone_inl :
    (CommRingCat.coproductCocone A B).inl = ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

