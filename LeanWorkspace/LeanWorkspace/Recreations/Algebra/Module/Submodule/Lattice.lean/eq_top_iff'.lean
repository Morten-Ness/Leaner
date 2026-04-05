import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p := eq_top_iff.trans ⟨fun h _ ↦ h trivial, fun h x _ ↦ h x⟩

