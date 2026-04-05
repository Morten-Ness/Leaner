import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem smul_quot [Algebra S R] {n : S} {a : R} :
    (n • ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (n • a)⟩ := (rfl)

