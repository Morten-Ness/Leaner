import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]; apply lie_mem_right; assumption

