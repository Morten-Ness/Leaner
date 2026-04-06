import Mathlib

variable {ι : Sort _}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem one_eq_range : (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R A) := by
  ext x
  simp [LinearMap.mem_range]
