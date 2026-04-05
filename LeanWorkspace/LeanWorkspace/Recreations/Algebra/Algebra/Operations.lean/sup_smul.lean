import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N := le_antisymm (Submodule.smul_le.mpr fun mn hmn p hp ↦ by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
    rw [add_smul]; exact add_mem_sup (Submodule.smul_mem_smul hm hp) <| Submodule.smul_mem_smul hn hp)
    (sup_le (Submodule.smul_mono_left le_sup_left) <| Submodule.smul_mono_left le_sup_right)

