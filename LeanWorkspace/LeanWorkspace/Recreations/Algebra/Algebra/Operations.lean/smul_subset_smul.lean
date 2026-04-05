import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_subset_smul : (↑I : Set A) • (↑N : Set M) ⊆ (↑(I • N) : Set M) := AddSubmonoid.smul_subset_smul

