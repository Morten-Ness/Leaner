import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem coe_set_smul : (I : Set A) • N = I • N := set_smul_eq_of_le _ _ _
    (fun _ _ hr hx ↦ Submodule.smul_mem_smul hr hx)
    (Submodule.smul_le.mpr fun _ hr _ hx ↦ mem_set_smul_of_mem_mem hr hx)

