import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable [FaithfulSMul R A]

theorem ker_unitsMap_spanSingleton :
    (Units.map (Submodule.spanSingleton R).toMonoidHom).ker =
    (Units.map (algebraMap R A).toMonoidHom).range := by
  ext; simpa [Units.ext_iff, eq_comm] using Submodule.span_singleton_eq_one_iff

