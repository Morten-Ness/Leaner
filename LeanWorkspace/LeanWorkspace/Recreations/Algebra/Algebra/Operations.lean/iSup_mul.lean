import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem iSup_mul (s : ι → Submodule R A) (t : Submodule R A) : (⨆ i, s i) * t = ⨆ i, s i * t := Submodule.iSup_smul

