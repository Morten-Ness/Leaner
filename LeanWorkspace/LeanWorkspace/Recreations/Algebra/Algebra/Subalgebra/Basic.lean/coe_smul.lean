import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := rfl

