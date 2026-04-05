import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem smul_one_eq_span (x : A) : x • (1 : Submodule R A) = span R {x} := by
  rw [Submodule.one_eq_span, smul_span, smul_set_singleton, smul_eq_mul, mul_one]

