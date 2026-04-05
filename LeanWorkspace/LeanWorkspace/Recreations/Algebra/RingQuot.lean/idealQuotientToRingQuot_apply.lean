import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type uR} [CommRing B]

theorem idealQuotientToRingQuot_apply (r : B → B → Prop) (x : B) :
    RingQuot.idealQuotientToRingQuot r (Ideal.Quotient.mk _ x) = mkRingHom r x := rfl

