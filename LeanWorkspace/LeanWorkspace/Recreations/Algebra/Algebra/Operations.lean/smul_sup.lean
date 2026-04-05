import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P := toAddSubmonoid_injective <| by
    simp only [Submodule.smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]

