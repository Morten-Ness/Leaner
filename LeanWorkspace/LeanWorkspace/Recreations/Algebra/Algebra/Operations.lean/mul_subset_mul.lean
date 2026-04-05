import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_subset_mul : (↑M : Set A) * (↑N : Set A) ⊆ (↑(M * N) : Set A) := Submodule.smul_subset_smul _ _

