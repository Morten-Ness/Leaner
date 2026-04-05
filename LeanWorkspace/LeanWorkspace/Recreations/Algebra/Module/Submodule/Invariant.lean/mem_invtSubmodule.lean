import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem mem_invtSubmodule {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p ≤ p.comap f := Iff.rfl

