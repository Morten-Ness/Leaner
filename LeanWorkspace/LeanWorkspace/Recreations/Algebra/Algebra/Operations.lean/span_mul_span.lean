import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem span_mul_span : span R S * span R T = span R (S * T) := by
  rw [Submodule.mul_eq_map₂]; apply map₂_span_span

