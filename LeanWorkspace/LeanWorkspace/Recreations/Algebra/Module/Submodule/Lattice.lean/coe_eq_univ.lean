import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem coe_eq_univ : (p : Set M) = Set.univ ↔ p = ⊤ := by
  rw [iff_comm, ← SetLike.coe_set_eq, Submodule.top_coe]

