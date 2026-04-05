import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_eq_span_mul_set (s t : Submodule R A) : s * t = span R ((s : Set A) * (t : Set A)) := by
  rw [Submodule.mul_eq_map₂]; exact map₂_eq_span_image2 _ s t

