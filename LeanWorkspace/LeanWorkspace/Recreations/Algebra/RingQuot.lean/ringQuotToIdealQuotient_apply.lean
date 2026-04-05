import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

variable [Semiring T]

variable {B : Type uR} [CommRing B]

theorem ringQuotToIdealQuotient_apply (r : B → B → Prop) (x : B) :
    RingQuot.ringQuotToIdealQuotient r (mkRingHom r x) = Ideal.Quotient.mk (Ideal.ofRel r) x := by
  simp_rw [RingQuot.ringQuotToIdealQuotient, lift_def, preLift_def, mkRingHom_def]
  rfl

