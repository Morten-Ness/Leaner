import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

theorem prod_top : (Subalgebra.prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp

