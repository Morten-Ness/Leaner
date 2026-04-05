import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem Rel.add_right {r : R → R → Prop} ⦃a b c : R⦄ (h : Rel r b c) : Rel r (a + b) (a + c) := by
  rw [add_comm a b, add_comm a c]
  exact Rel.add_left h

