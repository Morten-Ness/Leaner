import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ ≤ ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply LieSubmodule.mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ ≤ ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [LieSubmodule.lieIdeal_oper_eq_span, lieSpan_le]
  rintro m ⟨x, ⟨n, hn⟩, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hn ⊢
  rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆; constructor; · apply LieSubmodule.lie_coe_mem_lie
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆; constructor; · apply LieSubmodule.lie_coe_mem_lie
  simp [← h, ← hn']

