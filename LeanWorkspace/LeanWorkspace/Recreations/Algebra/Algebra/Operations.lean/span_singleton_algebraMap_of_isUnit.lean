import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem span_singleton_algebraMap_of_isUnit {r : R} (h : IsUnit r) :
    span R {algebraMap R A r} = 1 := by
  conv_rhs => rw [Submodule.one_eq_span, ← span_singleton_smul_eq h, ← algebraMap_eq_smul_one]

