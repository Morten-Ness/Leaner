import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι → Submodule R M} :
    I • (⨆ i, t i) = ⨆ i, I • t i := toAddSubmonoid_injective <| by
    simp only [Submodule.smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]

