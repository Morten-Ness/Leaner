import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_span_singleton_mul {x y : A} : x ∈ span R {y} * P ↔ ∃ z ∈ P, y * z = x := by
  simp_rw [Submodule.mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]

