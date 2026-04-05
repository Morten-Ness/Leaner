import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mem_mul_span_singleton {x y : A} : x ∈ P * span R {y} ↔ ∃ z ∈ P, z * y = x := by
  simp_rw [Submodule.mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]

