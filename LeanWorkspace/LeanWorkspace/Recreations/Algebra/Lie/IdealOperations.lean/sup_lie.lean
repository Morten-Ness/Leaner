import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ ≤ ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply LieSubmodule.mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ ≤ ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [LieSubmodule.lieIdeal_oper_eq_span, lieSpan_le]
  rintro m ⟨⟨x, hx⟩, n, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hx ⊢
  rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆; constructor; · apply LieSubmodule.lie_coe_mem_lie
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆; constructor; · apply LieSubmodule.lie_coe_mem_lie
  simp [← h, ← hx']

