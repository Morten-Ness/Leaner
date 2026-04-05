import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 := let ⟨b, hb₁, hb₂⟩ := Submodule.ne_bot_iff p.mp h
  ⟨b, hb₁, hb₂⟩

-- FIXME: we default PUnit to PUnit.{1} here without the explicit universe annotation

