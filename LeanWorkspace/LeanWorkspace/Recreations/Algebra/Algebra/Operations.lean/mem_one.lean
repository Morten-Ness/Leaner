import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_one {x : A} : x ∈ (1 : Submodule R A) ↔ ∃ y, algebraMap R A y = x := by
  simp [Submodule.one_eq_range]

