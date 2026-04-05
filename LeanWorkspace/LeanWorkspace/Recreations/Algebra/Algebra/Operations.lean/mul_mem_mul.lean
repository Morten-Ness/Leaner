import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N := Submodule.smul_mem_smul hm hn

