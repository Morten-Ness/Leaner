import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem one_smul : (1 : Submodule R A) • N = N := by
  refine le_antisymm (Submodule.smul_le.mpr fun r hr m hm ↦ ?_) fun m hm ↦ ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply, smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact Submodule.smul_mem_smul (Submodule.one_le.mp le_rfl) hm

