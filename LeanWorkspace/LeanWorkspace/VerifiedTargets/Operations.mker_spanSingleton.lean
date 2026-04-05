import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable [FaithfulSMul R A]

theorem mker_spanSingleton :
    MonoidHom.mker (Submodule.spanSingleton R) = (IsUnit.submonoid R).map (algebraMap R A) := by
  ext; simp_rw [Submonoid.mem_map, IsUnit.mem_submonoid_iff, IsUnit, existsAndEq, true_and, eq_comm]
  exact Submodule.span_singleton_eq_one_iff

