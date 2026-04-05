import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥ := by
  rw [subsingleton_iff, Submodule.eq_bot_iff]
  refine ⟨fun h x hx ↦ by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simp [h x hx, h y hy]⟩

