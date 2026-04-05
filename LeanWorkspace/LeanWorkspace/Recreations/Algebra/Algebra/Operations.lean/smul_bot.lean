import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ := toAddSubmonoid_injective <| AddSubmonoid.addSubmonoid_smul_bot _

