import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem toSpanSingleton_one_eq_algebraLinearMap :
    toSpanSingleton R A 1 = Algebra.linearMap R A := by ext; simp

