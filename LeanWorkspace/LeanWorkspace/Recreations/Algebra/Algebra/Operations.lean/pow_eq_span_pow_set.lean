import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem pow_eq_span_pow_set (n : ℕ) : M ^ n = span R ((M : Set A) ^ n) := by
  rw [← Submodule.span_pow, span_eq]

