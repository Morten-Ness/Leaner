import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U := by
  constructor
  · intro h
    ext x
    change x ∈ S.toSubsemiring ↔ x ∈ U.toSubsemiring
    simpa [h]
  · intro h
    simpa [h]
