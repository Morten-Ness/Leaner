import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : Submodule R A) := by
  simp [Submodule.one_eq_range]

