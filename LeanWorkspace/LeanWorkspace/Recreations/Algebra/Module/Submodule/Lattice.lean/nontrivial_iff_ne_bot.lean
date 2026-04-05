import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem nontrivial_iff_ne_bot : Nontrivial p ↔ p ≠ ⊥ := by
  rw [iff_not_comm, not_nontrivial_iff_subsingleton, Submodule.subsingleton_iff_eq_bot]

