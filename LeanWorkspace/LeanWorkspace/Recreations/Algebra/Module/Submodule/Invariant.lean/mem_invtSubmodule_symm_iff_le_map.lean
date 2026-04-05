import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} :
    p ∈ Module.End.invtSubmodule f.symm ↔ p ≤ p.map (f : M →ₗ[R] M) := (Module.End.mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

