import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem Rel.neg {R : Type uR} [Ring R] {r : R → R → Prop} ⦃a b : R⦄ (h : Rel r a b) :
    Rel r (-a) (-b) := by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, Rel.mul_right h]

