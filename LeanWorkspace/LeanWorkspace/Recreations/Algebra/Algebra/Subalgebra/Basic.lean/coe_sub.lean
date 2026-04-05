import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl

