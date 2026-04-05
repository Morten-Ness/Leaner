import Mathlib

variable {k G H : Type*}

variable {A : Type*}

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

theorem domCongr_refl :
    SkewMonoidAlgebra.domCongrAlg k A (e := MulEquiv.refl G) (fun _ _ ↦ rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  aesop

