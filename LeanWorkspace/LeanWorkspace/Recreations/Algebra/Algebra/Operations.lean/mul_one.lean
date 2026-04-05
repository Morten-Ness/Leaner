import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_one : M * 1 = M := by
  conv_lhs => rw [Submodule.one_eq_span, ← span_eq M]
  rw [Submodule.span_mul_span]
  simp

