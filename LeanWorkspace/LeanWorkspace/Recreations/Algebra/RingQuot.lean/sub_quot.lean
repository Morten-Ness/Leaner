import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

variable (r : R → R → Prop)

theorem sub_quot {R : Type uR} [Ring R] (r : R → R → Prop) {a b} :
    (⟨Quot.mk _ a⟩ - ⟨Quot.mk _ b⟩ : RingQuot r) = ⟨Quot.mk _ (a - b)⟩ := (rfl)

