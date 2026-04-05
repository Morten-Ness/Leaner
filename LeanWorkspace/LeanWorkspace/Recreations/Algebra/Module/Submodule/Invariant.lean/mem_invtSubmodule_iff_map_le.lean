import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem mem_invtSubmodule_iff_map_le {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p.map f ≤ p := Submodule.map_le_iff_le_comap.symm

