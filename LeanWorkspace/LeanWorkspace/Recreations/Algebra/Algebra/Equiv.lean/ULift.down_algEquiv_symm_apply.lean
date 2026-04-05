import Mathlib

theorem ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    (ULift.algEquiv (R := R).symm a).down = a :=
  rfl

