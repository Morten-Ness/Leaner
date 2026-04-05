import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x ∈ P * Q) :
    ∃ T T' : Finset A, (T : Set A) ⊆ P ∧ (T' : Set A) ⊆ Q ∧ x ∈ span R (T * T' : Set A) := Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

