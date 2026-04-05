import Mathlib

variable (A B : CommRingCat.{u})

theorem coproductCocone_inr :
    (CommRingCat.coproductCocone A B).inr = ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

