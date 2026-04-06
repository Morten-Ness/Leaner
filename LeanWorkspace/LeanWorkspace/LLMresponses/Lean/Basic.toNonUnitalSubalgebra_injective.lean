import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toNonUnitalSubalgebra_injective : Function.Injective
    (Subalgebra.toNonUnitalSubalgebra : Subalgebra R A → NonUnitalSubalgebra R A) := by
  intro S T h
  ext x
  exact SetLike.ext_iff.mp h x
