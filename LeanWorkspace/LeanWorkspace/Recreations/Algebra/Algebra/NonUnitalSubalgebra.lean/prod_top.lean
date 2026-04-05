import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable (S₁ : NonUnitalSubalgebra R B)

variable [IsScalarTower R A A] [SMulCommClass R A A] [IsScalarTower R B B] [SMulCommClass R B B]

theorem prod_top : (NonUnitalSubalgebra.prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤ := by ext; simp

