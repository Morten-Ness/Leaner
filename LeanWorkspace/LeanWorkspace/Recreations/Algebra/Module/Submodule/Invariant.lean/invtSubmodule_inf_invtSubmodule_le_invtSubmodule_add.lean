import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add :
    f.invtSubmodule ⊓ g.invtSubmodule ≤ (f + g).invtSubmodule := fun p ⟨hfp, hgp⟩ _ hx ↦ p.add_mem (hfp hx) (hgp hx)

