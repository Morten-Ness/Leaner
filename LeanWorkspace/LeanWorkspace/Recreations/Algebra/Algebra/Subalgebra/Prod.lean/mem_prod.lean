import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x ∈ Subalgebra.prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod

