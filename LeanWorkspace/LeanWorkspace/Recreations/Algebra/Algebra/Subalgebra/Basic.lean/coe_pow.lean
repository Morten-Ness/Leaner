import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = (x : A) ^ n := SubmonoidClass.coe_pow x n

