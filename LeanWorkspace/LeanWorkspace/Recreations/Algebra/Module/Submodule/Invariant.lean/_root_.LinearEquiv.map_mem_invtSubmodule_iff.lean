import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem _root_.LinearEquiv.map_mem_invtSubmodule_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R N}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map (e : M →ₗ[R] N) ∈ f.invtSubmodule ↔ p ∈ (e.symm.conj f).invtSubmodule := by
  simp [← e.map_mem_invtSubmodule_conj_iff]

