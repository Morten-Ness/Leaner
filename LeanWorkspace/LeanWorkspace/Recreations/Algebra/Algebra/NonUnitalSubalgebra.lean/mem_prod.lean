import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable (S₁ : NonUnitalSubalgebra R B)

theorem mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B} :
    x ∈ NonUnitalSubalgebra.prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod

