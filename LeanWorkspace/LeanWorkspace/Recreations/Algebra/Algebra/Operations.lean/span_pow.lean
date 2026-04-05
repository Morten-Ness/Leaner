import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem span_pow (s : Set A) : ∀ n : ℕ, span R s ^ n = span R (s ^ n)
  | 0 => by rw [Submodule.pow_zero, Submodule.pow_zero, Submodule.one_eq_span_one_set]
  | n + 1 => by rw [Submodule.pow_succ, Submodule.pow_succ, span_pow s n, Submodule.span_mul_span]
