import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem zero_quot : (⟨Quot.mk _ 0⟩ : RingQuot r) = 0 := (rfl)

