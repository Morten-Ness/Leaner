import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 := Set.mem_singleton_iff

