import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem coe_algebraMap (c : RingCon A) (s : S) :
    (algebraMap S A s : c.Quotient) = algebraMap S c.Quotient s := rfl

