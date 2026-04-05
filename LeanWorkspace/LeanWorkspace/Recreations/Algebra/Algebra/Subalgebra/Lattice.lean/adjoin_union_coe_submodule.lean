import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_union_coe_submodule :
    Subalgebra.toSubmodule (Algebra.adjoin R (s ∪ t)) =
      Subalgebra.toSubmodule (Algebra.adjoin R s) * Subalgebra.toSubmodule (Algebra.adjoin R t) := by
  rw [Algebra.adjoin_eq_span, Algebra.adjoin_eq_span, Algebra.adjoin_eq_span, span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

