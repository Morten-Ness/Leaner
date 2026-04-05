import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem span_singleton_mul {x : A} {p : Submodule R A} :
    Submodule.span R {x} * p = x • p := ext fun _ ↦ Submodule.mem_span_singleton_mul

