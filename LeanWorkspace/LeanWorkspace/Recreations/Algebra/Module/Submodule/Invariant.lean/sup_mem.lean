import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem sup_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊔ q ∈ f.invtSubmodule := Sublattice.sup_mem hp hq

