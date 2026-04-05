import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem bot_smul : (⊥ : Submodule R A) • N = ⊥ := le_bot_iff.mp <| Submodule.smul_le.mpr <| by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _

