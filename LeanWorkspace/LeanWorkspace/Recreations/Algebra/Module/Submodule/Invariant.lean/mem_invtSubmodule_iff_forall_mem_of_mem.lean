import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem mem_invtSubmodule_iff_forall_mem_of_mem {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ ∀ x ∈ p, f x ∈ p := Iff.rfl

