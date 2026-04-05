import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

