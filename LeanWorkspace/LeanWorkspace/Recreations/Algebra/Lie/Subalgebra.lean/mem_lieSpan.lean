import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem mem_lieSpan {x : L} : x ∈ LieSubalgebra.lieSpan R L s ↔ ∀ K : LieSubalgebra R L, s ⊆ K → x ∈ K := by
  rw [← SetLike.mem_coe, LieSubalgebra.lieSpan, LieSubalgebra.coe_sInf]
  exact Set.mem_iInter₂

