import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem iSup_smul {ι : Sort*} {t : ι → Submodule R A} {N : Submodule R M} :
    (⨆ i, t i) • N = ⨆ i, t i • N := le_antisymm (Submodule.smul_le.mpr fun t ht s hs ↦ iSup_induction _ (motive := (· • s ∈ _)) ht
    (fun i t ht ↦ mem_iSup_of_mem i <| Submodule.smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y ↦ by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i ↦ Submodule.smul_mono_left <| le_iSup _ i)

