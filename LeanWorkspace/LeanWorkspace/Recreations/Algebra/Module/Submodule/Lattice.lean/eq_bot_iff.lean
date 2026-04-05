import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) := ⟨fun h ↦ h.symm ▸ fun _ hx ↦ (Submodule.mem_bot R).mp hx,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot R).mpr (h x hx)⟩

