FAIL
import Mathlib

universe u v uι

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem mul_top_eq_top_of_mul_eq_one (h : N * P = 1) : N * ⊤ = ⊤ := by
  rw [show (⊤ : Submodule R A) = P * ⊤ by
    rw [← h, mul_assoc, one_mul]]
  rw [mul_assoc, h, one_mul]
