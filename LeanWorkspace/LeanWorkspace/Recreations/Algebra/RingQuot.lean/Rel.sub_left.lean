import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem Rel.sub_left {R : Type uR} [Ring R] {r : R → R → Prop} ⦃a b c : R⦄ (h : Rel r a b) :
    Rel r (a - c) (b - c) := by simp only [sub_eq_add_neg, h.add_left]

