import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem pow_quot {a} {n : ℕ} : (⟨Quot.mk _ a⟩ ^ n : RingQuot r) = ⟨Quot.mk _ (a ^ n)⟩ := (rfl)

