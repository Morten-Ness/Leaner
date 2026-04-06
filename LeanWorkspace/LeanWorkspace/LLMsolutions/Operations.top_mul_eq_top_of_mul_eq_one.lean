FAIL
import Mathlib

universe uι u v

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem top_mul_eq_top_of_mul_eq_one (h : N * P = 1) : ⊤ * P = ⊤ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    rw [← Submodule.one_eq_top]
    rw [← h]
    refine Submodule.mul_le.2 ?_ hx
    intro a ha b hb
    exact Submodule.mul_mem_mul ha hb
