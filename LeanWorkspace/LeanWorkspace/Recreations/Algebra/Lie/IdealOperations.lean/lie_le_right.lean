import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem lie_le_right : ⁅I, N⁆ ≤ N := by
  rw [LieSubmodule.lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property

