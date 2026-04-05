import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅(x : L), m⁆ = 0 := by
  rw [LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn

