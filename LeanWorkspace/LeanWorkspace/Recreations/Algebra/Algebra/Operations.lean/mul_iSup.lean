import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem mul_iSup (t : Submodule R A) (s : ι → Submodule R A) : (t * ⨆ i, s i) = ⨆ i, t * s i := Submodule.smul_iSup

