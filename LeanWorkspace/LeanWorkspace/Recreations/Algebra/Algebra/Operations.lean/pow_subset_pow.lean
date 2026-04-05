import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem pow_subset_pow {n : ℕ} : (↑M : Set A) ^ n ⊆ ↑(M ^ n : Submodule R A) := trans AddSubmonoid.pow_subset_pow (Submodule.le_pow_toAddSubmonoid M)

