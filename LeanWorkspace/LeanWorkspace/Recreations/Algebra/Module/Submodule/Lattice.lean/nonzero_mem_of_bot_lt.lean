import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 := let ⟨b, hb₁, hb₂⟩ := Submodule.ne_bot_iff p.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩

