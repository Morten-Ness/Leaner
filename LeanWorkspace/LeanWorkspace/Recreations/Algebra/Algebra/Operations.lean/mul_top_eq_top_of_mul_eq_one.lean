import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem mul_top_eq_top_of_mul_eq_one (h : N * P = 1) : N * ⊤ = ⊤ := top_unique <| by
    conv_lhs => rw [← Submodule.one_mul ⊤, ← h, mul_assoc]
    exact Submodule.smul_mono le_rfl le_top

